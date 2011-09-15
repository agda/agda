{-# LANGUAGE CPP #-}
module Agda.Compiler.Epic.Forcing where

import Control.Applicative
import Control.Arrow (first, second)
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
removeForced :: CompiledClauses -> Type -> Compile TCM CompiledClauses
removeForced cc typ = do
  TelV tele _ <- lift $ telView typ
  remForced cc tele

-- | Returns the type of a constructor given its name
constrType :: QName -> Compile TCM Type
constrType q = do
    map <- lift (gets (sigDefinitions . stImports))
    return $ maybe __IMPOSSIBLE__ defType (M.lookup q map)

-- | Returns how many parameters a datatype has
dataParameters :: QName -> Compile TCM Nat
dataParameters name = do
    m <- lift (gets (sigDefinitions . stImports))
    return $ maybe __IMPOSSIBLE__ (defnPars . theDef) (M.lookup name m)
  where
    defnPars :: Defn -> Nat
    defnPars (Datatype {dataPars = p}) = p
    defnPars (Record   {recPars  = p}) = p
    defnPars _                         = 0 -- Not so sure about this.

-- | Is variable n used in a CompiledClause?
isIn :: Nat -> CompiledClauses -> Compile TCM Bool
n `isIn` Case i brs | n == fromIntegral i = return True
                    | otherwise = n `isInCase` (fromIntegral i, brs)
n `isIn` Done _ t = return $ n `isInTerm` t
n `isIn` Fail     = return $ False

isInCase :: Nat -> (Nat, Case CompiledClauses) -> Compile TCM Bool
n `isInCase` (i, Branches { conBranches    = cbrs
                          , litBranches    = lbrs
                          , catchAllBranch = cabr}) = do
    cbrs' <- (or <$>) $ forM (M.toList cbrs) $ \ (constr, cc) -> do
        if i < n
          then do
            par <- fromIntegral <$> getConPar constr
            (n + par - 1) `isIn` cc
          else n `isIn` cc

    lbrs' <- (or <$>) $ forM (M.toList lbrs) $ \ (_, cc) ->
        (if i < n
           then (n - 1)
           else n) `isIn` cc

    cabr' <- case cabr of
        Nothing -> return False
        Just cc -> n `isIn` cc
    return (cbrs' || lbrs' || cabr')


isInTerm :: Nat -> Term -> Bool
n `isInTerm` term = let recs = any (isInTerm n . unArg) in case term of
   Var i as -> i == n || recs as
   Lam _ ab -> (n+1) `isInTerm` absBody ab
   Lit _    -> False
   Level l  -> isInLevel n l
   Def _ as -> recs as
   Con _ as -> recs as
   Pi a b   -> n `isInTerm` unEl (unArg a) || (n+1) `isInTerm` unEl (absBody b)
   Fun a b  -> n `isInTerm` unEl (unArg a) || n `isInTerm` unEl b
   Sort sor -> False -- ?
   MetaV meta as -> recs as
   DontCare _ -> False

isInLevel :: Nat -> Level -> Bool
isInLevel n (Max as) = any (isInPlus n) as
  where
    isInPlus _ ClosedLevel{} = False
    isInPlus n (Plus _ l) = isInAtom n l
    isInAtom n l = case l of
      MetaLevel _ as -> any (isInTerm n . unArg) as
      NeutralLevel v -> isInTerm n v
      BlockedLevel _ v -> isInTerm n v
      UnreducedLevel v -> isInTerm n v

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
insertTele ::  Int        -- ^ ABS `pos` in tele
            -> Maybe Type -- ^ If Just, it is the type to insert patterns from
                          --   is nothing if we only want to delete a binding.
            -> Term       -- ^ Term to replace at pos
            -> Telescope  -- ^ The telescope `tele` where everything is at
            -> Compile TCM ( Telescope
                         , ( Type
                           , Type
                           )
                         )
                -- ^ Returns (resulting telescope, the type at pos in tele, the
                --   return type of the inserted type).
insertTele 0 ins term (ExtendTel t to) = do
    t' <- lift $ normalise t
    let Def st arg = unEl . unArg $ t'
    -- Apply the parameters of the type of t
    -- Because: parameters occurs in the type of constructors but are not bound by it.
    pars <- dataParameters st
    TelV ctele ctyp <- lift $ telView $ maybe (unArg t')
                            (`apply` take (fromIntegral pars) arg) ins

    () <- if length (take (fromIntegral pars) arg) == fromIntegral pars
        then return ()
        else __IMPOSSIBLE__
    -- we deal with absBody to directly since we remove t
    return ( ctele +:+  (subst term $ raiseFrom 1 (size ctele) (absBody to))
           , (raise (size ctele) $ unArg t , ctyp)
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

unifyI :: Telescope -> [Nat] -> Type -> Args -> Args -> Compile TCM [Maybe Term]
unifyI tele flex typ a1 a2 = lift $ addCtxTel tele $ unifyIndices_ flex typ a1 a2

takeTele 0 _ = EmptyTel
takeTele n (ExtendTel t ts) = ExtendTel t ts {absBody = takeTele (n-1) (absBody ts) }
takeTele _ _ = __IMPOSSIBLE__

-- | Remove forced variables cased on in the current top-level case in the CompiledClauses
remForced ::
        CompiledClauses -- ^ Remove cases on forced variables in this
     -> Telescope       -- ^ The current context we are in
     -> Compile TCM CompiledClauses
remForced ccOrig tele = case ccOrig of
    Case n brs -> do
        -- Get all constructor branches
        cbs <- forM (M.toList $ conBranches brs) $ \(constr, cc) -> do
            par             <- getConPar  constr
            typ             <- constrType constr
            -- Update tele with the telescope from the constructor's type
            (tele', (ntyp, ctyp))   <- insertTele n (Just typ) (mkCon constr par) tele
            ntyp <- lift $ reduce ntyp
            ctyp <- lift $ reduce ctyp
            notForced       <- getIrrFilter constr
            -- Get the variables that are forced, relative to the position after constr
            forcedVars <- filterM ((`isIn` cc) . (flip subtract (fromIntegral $ n + par - 1)))
                        $ pairwiseFilter (map not notForced)
                        $ map fromIntegral [par-1,par-2..0]
            if null forcedVars
                then (,) constr <$> remForced cc tele'
                else do
                    unif <- case (unEl ntyp, unEl ctyp) of
                        (Def st a1, Def st' a2) | st == st' -> do
                            typPars <- fromIntegral <$> dataParameters st
                            setType <- constrType st
                            {-
                                We are splitting on C xs
                                we know that C : ts -> T ss ; for some T
                                we also know from tele that we are splitting on T as
                                we want to unify ss with as, but not taking into account
                                the Data parameters to T.
                            -}
                            unifyI (takeTele (n + par) tele')
                                   (map fromIntegral [0 .. n + par]) -- Don't unify the constructor arguments
                                   (setType `apply` take typPars a1)
                                   (drop typPars a1)
                                   (drop typPars a2)
                        x -> __IMPOSSIBLE__
                    -- we calculate the new tpos from n (the old one) by adding
                    -- how many more bindings we have
                    (,) constr <$> replaceForced (fromIntegral $ n + par, tele')
                                                 forcedVars
                                                 (cc, unif)

        lbs <- forM (M.toList $ litBranches brs) $ \(lit, cc) -> do
            -- We have one less binding
            (newTele, _) <- insertTele n Nothing (Lit lit) tele
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
replaceForced :: (Nat, Telescope) -> [Nat] -> (CompiledClauses, [Maybe Term])
              -> Compile TCM CompiledClauses
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
    termToBranch :: Nat -> Term -> Nat -> StateT FoldState (Compile TCM) ()
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
            ctyp <- lift (constrType c)

            modifyM $ \ st -> do
                (newTele , _) <- lift $ insertTele (fromIntegral caseVar) (Just ctyp)
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
        _ -> __IMPOSSIBLE__

-- Note: Absolute positions
raiseFromCC :: Nat -> Nat -> CompiledClauses -> CompiledClauses
raiseFromCC from add  cc = case cc of
    Case n (Branches cbr lbr cabr) -> Case (fromIntegral $ raiseN from add (fromIntegral n)) $
                                           Branches (M.map rec cbr)
                                                    (M.map rec lbr)
                                                    (fmap  rec cabr)
    Done i t -> Done (i ++ genericReplicate add NotHidden) $ raiseFrom from add t
    Fail     -> Fail
  where
    rec = raiseFromCC from add
    raiseN :: Nat -> Nat -> Nat -> Nat
    raiseN from add n | from <= n = n + add
                      | otherwise = n

-- | Substitute with the Substitution, this will adjust with the new bindings in the
--   CompiledClauses
substCC :: [Nat] -> CompiledClauses -> StateT FoldState (Compile TCM) CompiledClauses
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
