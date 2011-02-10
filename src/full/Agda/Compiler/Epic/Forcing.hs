module Agda.Compiler.Epic.Forcing where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans
import Data.List
import qualified Data.Map as M
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.Utils.List
import Agda.Utils.Size

import Agda.Compiler.Epic.CompileState hiding (conPars)
import Agda.Compiler.Epic.AuxAST(pairwiseFilter)

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Replace the uses of forced variables in a CompiledClauses with the function
--   arguments that they correspond to.
--   Note that this works on CompiledClauses where the term's variable indexes
--   have been reversed, which means that the case variables match the variables
--   in the term.
removeForced :: MonadTCM m => CompiledClauses -> Type -> Compile m CompiledClauses
removeForced cc typ = do
  TelV tele _ <- lift $ telView typ
  remForced cc tele

-- | Returns the type of a constructor given its name
constrType :: MonadTCM m => QName -> Compile m Type
constrType q = do
    map <- lift (gets (sigDefinitions . stImports))
    return $ maybe __IMPOSSIBLE__ defType (M.lookup q map)

-- | Returns how many parameters a datatype has
dataParameters :: MonadTCM m => QName -> Compile m Nat
dataParameters name = do
    m <- lift (gets (sigDefinitions . stImports))
    return $ maybe __IMPOSSIBLE__ (defnPars . theDef) (M.lookup name m)
  where
    defnPars :: Defn -> Nat
    defnPars (Datatype {dataPars = p}) = p
    defnPars (Record   {recPars  = p}) = p
    defnPars _                         = 0 -- Not so sure about this.

-- | Is variable n used in a CompiledClause?
isIn :: MonadTCM m => Nat -> CompiledClauses -> Compile m Bool
n `isIn` Case i brs | n == fromIntegral i = return True
                    | otherwise = or <$> mapM (n `isIn`) (M.elems (conBranches brs)
                                                       ++ M.elems (litBranches brs)
                                                       ++ maybeToList (catchAllBranch brs))
n `isIn` Done _ t = return $ n `isInTerm` t
n `isIn` Fail     = return $ False

isInTerm :: Nat -> Term -> Bool
n `isInTerm` term = let recs = any (isInTerm n . unArg) in case term of
   Var i as -> i == n || recs as
   Lam _ ab -> (n+1) `isInTerm` absBody ab
   Lit _    -> False
   Def _ as -> recs as
   Con _ as -> recs as
   Pi a b   -> n `isInTerm` unEl (unArg a) || (n+1) `isInTerm` unEl (absBody b)
   Fun a b  -> n `isInTerm` unEl (unArg a) || n `isInTerm` unEl b
   Sort sor -> False -- ?
   MetaV meta as -> False -- can't occur?
   DontCare -> False

{- |
insertTele i xs t tele
                  tpos
  tele := Gamma ; (i : T as) ; Delta
  n    := parameters T
  xs'  := xs `apply` (take n as)
becomes
                  tpos
  ( Gamma ; xs' ; Delta[i := t] --note that Delta still reference Gamma correctly
  , T as ^ (size xs')
  )

we raise the type since we have added xs' new bindings before Gamma, and as can
only bind to Gamma.
-}
insertTele :: MonadTCM m
            => Int     -- ^ ABS `pos` in tele
            -> Telescope -- ^ The telescope to insert
            -> Term      -- ^ Term to replace at pos
            -> Telescope -- ^ The telescope `tele` where everything is at
            -> Compile m ( Telescope -- ^ Resulting telescope
                         , Type      -- ^ The type at pos in tele
                         )
insertTele 0 ins term (ExtendTel t to) = do
    Def st arg <- unEl . unArg <$> lift (reduce t)
    -- Apply the parameters of the type of t
    -- Because: parameters occurs in the type of constructors but are not bound by it.
    pars <- dataParameters st
    let ins' = ins `apply` take (fromIntegral pars) arg
    () <- if length (take (fromIntegral pars) arg) == fromIntegral pars
        then return ()
        else __IMPOSSIBLE__
    -- we deal with absBody to directly since we remove t
    return ( ins' +:+  (subst term $ raiseFrom 1 (size ins') (absBody to))
           , raise (size ins') $ unArg t
           )
  where
    -- Append the telescope, we raise since we add a new binding and all the previous
    -- bindings need to be preserved
    (+:+) :: Telescope -> Telescope -> Telescope
    EmptyTel       +:+ t2 = t2
    ExtendTel t t1 +:+ t2 = ExtendTel t t1 {absBody = absBody t1 +:+ {-raise 1-} t2 }
-- This case is impossible since we are trying to split a variable outside the tele
insertTele n ins term EmptyTel = __IMPOSSIBLE__
insertTele n ins term (ExtendTel x xs) = do
    (xs', typ) <- insertTele (n - 1) ins term (absBody xs)
    return (ExtendTel x xs {absBody = xs'} , typ)

mkCon c n = Con c [ defaultArg $ Var (fromIntegral i) [] | i <- [n - 1, n - 2 .. 0] ]

-- | Remove forced variables cased on in the current top-level case in the CompiledClauses
remForced :: MonadTCM m
     => CompiledClauses -- ^ Remove cases on forced variables in this
     -> Telescope       -- ^ The current context we are in
     -> Compile m CompiledClauses
remForced ccOrig tele = case ccOrig of
    Case n brs -> do
        -- Get all constructor branches
        cbs <- forM (M.toList $ conBranches brs) $ \(constr, cc) -> do
            par             <- getConPar  constr
            typ             <- constrType constr
            TelV ctele ctyp <- lift $ telView typ
            -- Update tele with the telescope from the constructor's type
            (tele', ntyp)   <- insertTele n ctele (mkCon constr par) tele
            notForced       <- getIrrFilter constr
            -- Get the variables that are forced, relative to the position after constr
            forcedVars <- filterM ((`isIn` cc) . (flip subtract (fromIntegral $ n + par - 1)))
                        $ pairwiseFilter (map not notForced)
                        $ map fromIntegral [par-1,par-2..0]
            ntyp <- lift $ reduce ntyp
            ctyp <- lift $ reduce ctyp
            munif <- case (unEl ntyp, unEl ctyp) of
                (Def st a1, Def st' a2) | st == st' -> do
                    a1' <- mapM (lift . reduce) a1
                    typPars <- fromIntegral <$> dataParameters st
                    setType <- constrType st
                    {-
                        We are splitting on C xs
                        we know that C : ts -> T ss ; for some T
                        we also know from tele that we are splitting on T as
                        we want to unify ss with as, but not taking into account
                        the Data parameters to T.
                    -}
                    lift $ unifyIndices (map fromIntegral [par .. n + par]) -- Don't unify the constructor arguments
                                        (setType `apply` take typPars a1')
                                        (drop typPars a1')
                                        (drop typPars a2)
                x -> __IMPOSSIBLE__
            case (forcedVars, munif) of
              (_:_, Unifies unif) -> do
                  -- we calculate the new tpos from n (the old one) by adding
                  -- how many more bindings we have
                  (,) constr <$> replaceForced (fromIntegral $ n + par, tele')
                                               forcedVars
                                               (cc, unif)
              (_:_, NoUnify _ _ _) -> __IMPOSSIBLE__
              (_:_, DontKnow _)    -> __IMPOSSIBLE__
              ([], _) -> (,) constr <$> remForced cc tele'

        lbs <- forM (M.toList $ litBranches brs) $ \(lit, cc) -> do
            -- We have one less binding
            (newTele, _) <- insertTele n EmptyTel (Lit lit) tele
            (,) lit <$>  remForced cc newTele

        cabs <- case catchAllBranch brs of
            Nothing -> return Nothing
            Just cc -> Just <$> remForced cc tele

        return $ Case n brs { conBranches = M.fromList cbs
                            , litBranches = M.fromList lbs
                            , catchAllBranch = cabs }

    Done n t   -> return $ Done n t
    Fail       -> return Fail

data FoldState = FoldState
  { clauseToFix  :: CompiledClauses
  , clausesAbove :: CompiledClauses -> CompiledClauses
  , unification  :: [Maybe Term]
  , theTelescope :: Telescope
  , telePos      :: Nat
  } deriving Show

-- Some utility functions

foldM' :: Monad m => a -> [b] -> (a -> b -> m a) -> m a
foldM' z xs f = foldM f z xs

lift2 :: (MonadTrans t, Monad (t1 m), MonadTrans t1, Monad m) => m a -> t (t1 m) a
lift2 = lift . lift

modifyM :: (MonadState a m) => (a -> m a) -> m ()
modifyM f = get >>= f >>= put -- (>>= put) . (get >>=)

-- | replaceForced (tpos, tele) forcedVars (cc, unification)
--   For each forceVar dig out the corresponding case and continue to remForced.
replaceForced :: MonadTCM m
              => (Nat, Telescope) -> [Nat] -> (CompiledClauses, [Maybe Term])
              -> Compile m CompiledClauses
replaceForced (telPos, tele) forcedVars (cc, unif) = do
    let origSt = FoldState
                  { clauseToFix  = cc
                  , clausesAbove = id
                  , unification  = unif
                  , theTelescope = tele
                  , telePos      = telPos
                  }
    st <- flip execStateT origSt $ forM forcedVars $ \ forcedVar -> do
        unif <- gets unification
        let (caseVar, caseTerm) = findPosition forcedVar unif
        telPos <- gets telePos
        termToBranch (telPos - caseVar - 1) caseTerm forcedVar
    clausesAbove st <$> remForced (clauseToFix st) (theTelescope st)
  where
    {-
      In this function the following de Bruijn is:
        forcedVar : Relative
        caseVar : Absolute
        telePos : Absolute
    -}
    termToBranch :: MonadTCM m => Nat -> Term -> Nat -> StateT FoldState (Compile m) ()
    termToBranch caseVar caseTerm forcedVar = case caseTerm of
        Var i _ | i == forcedVar -> do
            telPos <- gets telePos
            let sub = [0..telPos - forcedVar - 2] ++ [caseVar] ++ [telPos - forcedVar..]
            modifyM $ \ st -> do
                newClauseToFix <- substCC sub (clauseToFix st)
                return st
                    { clauseToFix = newClauseToFix
                    , unification = substs (map (flip Var []) sub) (unification st)
                    }
                -- This is impossible since we have already looked and it should
                -- be the correct Var
                | otherwise -> __IMPOSSIBLE__
        Con c args -> do
            telPos <- gets telePos
            let (nextCaseVarInCon, nextCaseTerm) = findPosition forcedVar (map (Just . unArg) args)
                nextCaseVar = nextCaseVarInCon + caseVar
                newBinds    = fromIntegral $ length args - 1
                -- we have added newBinds new bindings and removed one before telePos
                nextTelePos = telPos + newBinds
            TelV ctele ctyp <- lift2 . telView =<< lift (constrType c)

            modifyM $ \ st -> do
                (newTele , _) <- lift $ insertTele (fromIntegral caseVar) ctele
                                        (mkCon c (length args)) (theTelescope st)
                -- We have to update the unifications-list so that we don't try
                -- to dig out the same again later.
                let newUnif = raiseFrom (telPos - caseVar) newBinds $
                        replaceAt (fromIntegral $ telPos - caseVar - 1)
                                  (unification st)
                                  (reverse $ map (Just . unArg) args)
                                  -- The variables in the unification-list is
                                  -- relative so we need to reverse the args
                                  -- so they get in the right place.
                return st
                    { clauseToFix  = raiseFromCC caseVar newBinds
                                                 (substCCBody caseVar
                                                 (Con c $ map (defaultArg . flip Var [])
                                                              [caseVar .. caseVar + newBinds])
                                                 (clauseToFix st))
                    , theTelescope = newTele
                    , unification  = newUnif
                    , telePos      = nextTelePos
                    }
            st <- get
            termToBranch nextCaseVar nextCaseTerm forcedVar
            modify $ \ st -> st
                { clausesAbove = Case (fromIntegral caseVar) . conCase c . (clausesAbove st)
                }
        _ -> __IMPOSSIBLE__ -- Ulf said so

-- Note: Absolute positions
raiseFromCC :: Nat -> Nat -> CompiledClauses -> CompiledClauses
raiseFromCC from add  cc = case cc of
    Case n (Branches cbr lbr cabr) -> Case (fromIntegral $ raiseN from add (fromIntegral n)) $
                                           Branches (M.map rec cbr)
                                                    (M.map rec lbr)
                                                    (fmap  rec cabr)
    Done i t -> Done (i + fromIntegral add) $ raiseFrom from add t
    Fail     -> Fail
  where
    rec = raiseFromCC from add
    raiseN :: Nat -> Nat -> Nat -> Nat
    raiseN from add n | from <= n = n + add
                      | otherwise = n

-- | Substitute with the Substitution, this will adjust with the new bindings in the
--   CompiledClauses
substCC :: MonadTCM m => [Nat] -> CompiledClauses -> StateT FoldState (Compile m) CompiledClauses
substCC ss cc = case cc of
    Done i t -> do
        return $ Done i (substs (map (flip Var []) ({-reverse $ take i -} ss)) t)
    Fail     -> return Fail
    Case n brs -> do
        {-
          In a Case split, if we should change n to m, then all the binders in
          this pattern should also change from being based on n to be based on m.
        -}
        cbs <- forM (M.toList $ conBranches brs) $ \ (c, br) -> do
            nargs <- lift2 $ constructorArity c
            let delta = (ss !! n) - fi n
                ss'   = take n ss
                      ++ [fi n + delta .. fi n + delta + nargs - 1]
                      ++ map (+ (nargs - 1)) (drop (n+1) ss)
            (,) c <$> substCC ss' br

        lbs <- forM (M.toList $ litBranches brs) $ \ (l, br) -> do
            -- We have one less binder here
            (,) l <$> substCC (replaceAt n ss []) br

        cabs <- case catchAllBranch brs of
            Nothing -> return Nothing
            Just br -> Just <$> substCC ss br

        return $ Case (fromIntegral (ss !! n))
                  Branches { conBranches    = M.fromList cbs
                           , litBranches    = M.fromList lbs
                           , catchAllBranch = cabs
                           }
  where
    fi = fromIntegral

-- | Substitute variable n for term t in the body of cc
substCCBody :: Nat -> Term -> CompiledClauses -> CompiledClauses
substCCBody n t cc = substsCCBody (vs [0..n - 1] ++ [t] ++ vs [n + 1..]) cc
  where vs = map (flip Var [])

-- | Perform a substitution in the body of cc
substsCCBody :: [Term] -> CompiledClauses -> CompiledClauses
substsCCBody ss cc = case cc of
    Case n brs -> Case n (substsCCBody ss <$> brs)
    Done i t -> Done i (substs ss t)
    Fail     -> Fail

-- | Find the location where a certain Variable index is by searching the constructors
--   aswell. i.e find a term that can be transformed into a pattern that contains the
--   same value the index. This fails if no such term is present.
findPosition :: Nat -> [Maybe Term] -> (Nat, Term)
findPosition var ts = let Just n = findIndex (maybe False pred) ts
                       in (fromIntegral n , fromJust $ ts !! n)
  where
    pred :: Term -> Bool
    pred t = case t of
      Var i _ | var == i -> True
      Con _ args         -> any (pred . unArg) args
      _                  -> False
