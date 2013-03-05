{-# LANGUAGE CPP, ScopedTypeVariables #-}
module Agda.Compiler.Epic.Forcing where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans

import Data.Char
import Data.List hiding (sort)
import qualified Data.Map as M
import Data.Maybe

import Agda.Syntax.Common
import qualified Agda.Syntax.Internal as SI
import Agda.Syntax.Literal
import Agda.Syntax.Position(noRange)
import Agda.Syntax.Internal(Tele(..), Telescope, Term, Abs(..), unAbs, absName, Type, Args, QName, unEl)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Rules.LHS.Problem (FlexibleVars, defaultFlexibleVar)
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Instantiate
import Agda.TypeChecking.Substitute
  (raiseFrom, raise, applySubst, apply, wkS, raiseS, dropS, (++#), TelV(..))
import qualified Agda.TypeChecking.Substitute as S
import Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size
import qualified Agda.Utils.HashMap as HM

import Agda.Compiler.Epic.AuxAST
import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.Epic
import Agda.Compiler.Epic.Interface
import qualified Agda.Compiler.Epic.FromAgda as FA

#include "../../undefined.h"
import Agda.Utils.Impossible


-- | Returns how many parameters a datatype has
dataParameters :: QName -> Compile TCM Nat
dataParameters = lift . dataParametersTCM

-- | Returns how many parameters a datatype has
dataParametersTCM :: QName -> TCM Nat
dataParametersTCM name = do
    m <- (gets (sigDefinitions . stImports))
    return $ maybe __IMPOSSIBLE__ (defnPars . theDef) (HM.lookup name m)
  where
    defnPars :: Defn -> Nat
    defnPars (Datatype {dataPars = p}) = p
    defnPars (Record   {recPars  = p}) = p
    defnPars d                         = 0 -- error (show d) -- __IMPOSSIBLE__ -- Not so sure about this.

report n s = do
  lift $ reportSDoc "epic.forcing" n s

piApplyM' :: Type -> Args -> TCM Type
piApplyM' t as = do
 {- reportSDoc "" 10 $ vcat
    [ text "piApplyM'"
    , text "type: " <+> prettyTCM t
    , text "args: " <+> prettyTCM as
    ]-}
  piApplyM t as

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
insertTele ::(QName, Args) -> Int        -- ^ ABS `pos` in tele
            -> Maybe Type -- ^ If Just, it is the type to insert patterns from
                          --   is nothing if we only want to delete a binding.
            -> Term       -- ^ Term to replace at pos
            -> Telescope  -- ^ The telescope `tele` where everything is at
            -> Compile TCM ( Telescope -- Resulting telescope
                           , ( Telescope
                             , Type -- The type at pos in tele
                             , Type -- The return Type of the inserted type
                             )
                           )
insertTele x 0 ins term (ExtendTel t to) = do
    t' <- lift $ normalise t
    report 12 $ vcat
      [ text "t' :" <+> prettyTCM t'
      , text "term:" <+> prettyTCM term
      , text "to:"   <+> prettyTCM (unAbs to)
      ]
    (st, arg) <- case SI.unEl . unDom $ t' of
            SI.Def st arg -> return (st, arg)
            s          -> do
              report 10 $ vcat
                [ text "ERROR!!!"
                , text "found: " <+> (text . show) s
                , text "ins"     <+> (prettyTCM . fromMaybe __IMPOSSIBLE__) ins
                ]
              return x
    -- Apply the parameters of the type of t
    -- Because: parameters occurs in the type of constructors but are not bound by it.
    pars <- dataParameters st
    report 10 $ text "apply in insertTele"
    TelV ctele ctyp <- lift $ telView =<< maybe (return $ unDom t')
                            (`piApplyM'` genericTake pars arg) ins
--                            (`piApplyM'` take (fromIntegral pars) arg) ins
{- OLD CODE:
    () <- if length (take (fromIntegral pars) arg) == fromIntegral pars
        then return ()
        else __IMPOSSIBLE__
-}
    when (genericLength arg < pars) __IMPOSSIBLE__
    -- we deal with absBody to directly since we remove t
    return ( ctele +:+  (S.subst term $ S.raiseFrom 1 (size ctele) (unAbs to))
           , (ctele, S.raise (size ctele) $ unDom t , ctyp)
           )
  where
    -- Append the telescope, we raise since we add a new binding and all the previous
    -- bindings need to be preserved
    (+:+) :: Telescope -> Telescope -> Telescope
    EmptyTel       +:+ t2 = t2
    ExtendTel t t1 +:+ t2 = ExtendTel t (Abs (absName t1) $ unAbs t1 +:+ {-raise 1-} t2 )
-- This case is impossible since we are trying to split a variable outside the tele
insertTele x n ins term EmptyTel = __IMPOSSIBLE__
insertTele er n ins term (ExtendTel x xs) = do
    (xs', typ) <- insertTele er (n - 1) ins term (unAbs xs)
    return (ExtendTel x $ Abs (absName xs) xs' , typ)

mkCon c n = SI.Con c [ defaultArg $ SI.Var (fromIntegral i) [] | i <- [n - 1, n - 2 .. 0] ]

unifyI :: Telescope -> FlexibleVars -> Type -> Args -> Args -> Compile TCM [Maybe Term]
unifyI tele flex typ a1 a2 = lift $ addCtxTel tele $ unifyIndices_ flex typ a1 a2

takeTele 0 _ = EmptyTel
takeTele n (ExtendTel t ts) = ExtendTel t $ Abs (absName ts) $ takeTele (n-1) (unAbs ts)
takeTele _ _ = __IMPOSSIBLE__

-- | Main function for removing pattern matching on forced variables
remForced :: [Fun] -> Compile TCM [Fun]
remForced fs = do
    defs <- lift (gets (sigDefinitions . stImports))
    forM fs $ \f -> case f of
        Fun{} -> case funQName f >>= flip HM.lookup defs of
            Nothing -> __IMPOSSIBLE__
            Just def -> do
                TelV tele _ <- lift $ telView (defType def)
                report 10 $ vcat
                  [ text "compiling fun" <+> (text . show) (funQName f)
                  ]
                e <- forcedExpr (funArgs f) tele (funExpr f)
                report 10 $ vcat
                  [ text "compilied fun" <+> (text . show) (funQName f)
                  , text "before:" <+> (text . prettyEpic) (funExpr f)
                  , text "after:" <+> (text . prettyEpic) e
                  ]
                return $ f { funExpr = e}
        EpicFun{} -> return f

-- | For a given expression, in a certain telescope (the list of Var) is a mapping
-- of variable name to the telescope.
forcedExpr :: [Var] -> Telescope -> Expr -> Compile TCM Expr
forcedExpr vars tele expr = case expr of
    Var _ -> return expr
    Lit _ -> return expr
    Lam x e -> Lam x <$> rec e -- necessary?
    Con t q es -> Con t q <$> mapM rec es
    App v es -> App v <$> mapM rec es
    If a b c -> If <$> rec a <*> rec b <*> rec c
    Let v e1 e2 -> Let v <$> rec e1 <*> rec e2
    Lazy e -> Lazy <$> rec e
    UNIT   -> return expr
    IMPOSSIBLE -> return expr
    Case v@(Var x) brs -> do
        let n = fromMaybe __IMPOSSIBLE__ $ elemIndex x vars
        (Case v <$>) . forM brs $ \ br -> case br of
            BrInt i e -> do
              (tele'', _) <-  insertTele __IMPOSSIBLE__ n Nothing (SI.Lit (LitChar noRange (chr i))) tele
              BrInt i <$> forcedExpr (replaceAt n vars []) tele'' e

            Default e -> Default <$> rec e
            Branch t constr as e -> do
                typ <- getType constr
                forc <- getForcedArgs constr
                (tele'', (_, ntyp, ctyp)) <- insertTele __IMPOSSIBLE__ n (Just typ)
                                                        (mkCon constr (length as)) tele
                ntyp <- lift $ reduce ntyp
                ctyp <- lift $ reduce ctyp

                if null (forced forc as)
                  then Branch t constr as <$> forcedExpr (replaceAt n vars as) tele'' e
                  else do
                    -- unify the telescope type with the return type of the constructor
                    unif <- case (unEl ntyp, unEl ctyp) of
                        (SI.Def st a1, SI.Def st' a2) | st == st' -> do
                            typPars <- dataParameters st
                            setType <- getType st
                            report 10 $ vcat
                              [ text "ntyp:" <+> prettyTCM ntyp
                              , text "ctyp:" <+> prettyTCM ctyp
                              ]
                            unifyI (takeTele (n + length as) tele'')
                                   (map defaultFlexibleVar [0 .. n + length as])
                                   (setType `apply` take typPars a1)
                                   (drop typPars a1)
                                   (drop typPars a2)
                        _ -> __IMPOSSIBLE__
                    let
                        lower = wkS (-1) . dropS 1
                        subT 0 tel = let ss = [fromMaybe (SI.Var n []) t
                                                | (n , t) <- zip [0..] unif] ++#
                                              raiseS (length unif)
                                      in (applySubst ss tel, lower ss)
                        subT n (ExtendTel a t) = let
                               (tb' , ss) = subT (n - 1) (unAbs t)
                            in (ExtendTel a $ Abs (absName t) tb', lower ss)
                        subT _ _ = __IMPOSSIBLE__
                        (tele'''', _) = subT (n + length as) tele''
                    report 10 $ nest 2 $ vcat
                      [ text "remforced"
                      , text "tele=" <+> prettyTCM tele''
                      , text "tele'=" <+> prettyTCM tele''''
                      , text "unif=" <+> (text . show) unif
                      , text "forced=" <+> (text . show) (forced forc as)
                      , text "constr" <+> prettyTCM constr
                      ]
                    -- replace all forced variables found using the unification
                    Branch t constr as <$>
                        replaceForced (replaceAt n vars as, reverse $ take n vars ++ as)
                                      (tele'''') (forced forc as) unif e
    _ -> __IMPOSSIBLE__
  where
    rec = forcedExpr vars tele

-- | replace the forcedVar with pattern matching from the outside.
replaceForced :: ([Var],[Var]) -> Telescope -> [Var] -> [Maybe SI.Term] -> Expr -> Compile TCM Expr
replaceForced (vars,_) tele [] _ e = forcedExpr vars tele e
replaceForced (vars,uvars) tele (fvar : fvars) unif e = do
    let n = fromMaybe __IMPOSSIBLE__ $ elemIndex fvar uvars
    mpos <- findPosition n unif
    case mpos of
        Nothing -> case unif !! n of
            Nothing | fvar `notElem` fv e ->
              replaceForced (vars, uvars) tele fvars unif e
            Nothing -> do
              report 10 $ vcat
                [ text "failure comming!"
                , text "unif" <+> (text . show) unif
                , text "n" <+> (text . show) n
                , text "fvar" <+> (text fvar)
                , text "fv" <+> (text . show) (fv e)
                ]
              __IMPOSSIBLE__
            Just t  -> do
                v <- newName
                te <- FA.substTerm uvars t
                subst fvar v <$> replaceForced (vars, uvars)
                                               tele fvars unif (Let v te e)
        Just (pos , term) -> do
            (build, v) <- buildTerm (uvars !! pos) n term
            build . subst fvar v <$> replaceForced (vars, uvars) tele fvars unif
                                     e
  where
    sub fvar v = map $ \x -> if x == fvar then v else x

-- | Given a term containg the forced var, dig out the variable by inserting
-- the proper case-expressions.
buildTerm :: Var -> Nat -> Term -> Compile TCM (Expr -> Expr, Var)
buildTerm var idx (SI.Var i _) | idx == i = return (id, var)
buildTerm var idx (SI.Con c args) = do
    vs <- replicateM (length args) newName
    (pos , arg) <- fromMaybe __IMPOSSIBLE__ <$> findPosition idx (map (Just . unArg) args)
    (fun' , v) <- buildTerm (vs !! pos) idx arg
    tag <- getConstrTag c
    let fun e = casee (Var var) [Branch tag c vs e]
    return (fun . fun' , v)
buildTerm _ _ _ = __IMPOSSIBLE__


-- | Find the location where a certain Variable index is by searching the constructors
--   aswell. i.e find a term that can be transformed into a pattern that contains the
--   same value the index. This fails if no such term is present.
findPosition :: Nat -> [Maybe SI.Term] -> Compile TCM (Maybe (Nat, SI.Term))
findPosition var ts = (listToMaybe . catMaybes <$>) . forM (zip [0..] ts) $ \ (n, mt) -> do
    ifM (maybe (return False) pred mt)
        (return (Just (n, fromMaybe __IMPOSSIBLE__ mt)))
        (return Nothing)
  where
    pred :: Term -> Compile TCM Bool
    pred t = case t of
      SI.Var i _ | var == i -> return True
      SI.Con c args         -> do
          forc <- getForcedArgs c
          or <$> mapM (pred . unArg) (notForced forc args)
      _                  -> return False
