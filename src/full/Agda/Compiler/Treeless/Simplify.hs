{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
module Agda.Compiler.Treeless.Simplify (simplifyTTerm) where

import Control.Arrow (first, second, (***))
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Traversable (traverse)

import Agda.Syntax.Treeless
import Agda.Syntax.Internal (Substitution'(..))
import Agda.Syntax.Literal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Substitute
import Agda.Utils.Maybe

import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Pretty
import Agda.Utils.Pretty

import Agda.Utils.Impossible
#include "undefined.h"

type S = Reader (Substitution' TTerm)

runS :: S a -> a
runS m = runReader m IdS

lookupVar :: Int -> S TTerm
lookupVar i = asks (`lookupS` i)

underLams :: Int -> S a -> S a
underLams i = local (liftS i)

underLam :: S a -> S a
underLam = underLams 1

underLet :: TTerm -> S a -> S a
underLet u = local $ \rho -> wkS 1 $ composeS rho (singletonS 0 u)

data FunctionKit = FunctionKit
  { modAux, divAux :: Maybe QName }

simplifyTTerm :: TTerm -> TCM TTerm
simplifyTTerm t = do
  modAux <- getBuiltinName builtinNatModSucAux
  divAux <- getBuiltinName builtinNatDivSucAux
  return $ runS $ simplify FunctionKit{ modAux = modAux, divAux = divAux } t

simplify :: FunctionKit -> TTerm -> S TTerm
simplify FunctionKit{..} = simpl
  where
    simpl t = case t of

      TDef{}         -> pure t
      TPrim{}        -> pure t

      TVar x  -> do
        v <- lookupVar x
        pure $ if isAtomic v then v else t

      TApp (TDef f) [TLit (LitNat _ 0), m, n, m']
        | m == m', Just f == divAux -> simpl $ tOp PDiv n (tPlusK 1 m)
        | m == m', Just f == modAux -> simpl $ tOp PMod n (tPlusK 1 m)

      TApp (TPrim op) args -> do
        args <- mapM simpl args
        let inline (TVar x) = lookupVar x
            inline u        = pure u
        inlined <- mapM inline args
        let nosimpl = TApp (TPrim op) args
        pure $ fromMaybe nosimpl $ simplPrim $ TApp (TPrim op) inlined

      TApp f es      -> do
        f  <- simpl f
        es <- traverse simpl es
        tApp f es
      TLam b         -> TLam <$> underLam (simpl b)
      TLit{}         -> pure t
      TCon{}         -> pure t
      TLet e b       -> do
        e <- simpl e
        TLet e <$> underLet e (simpl b)

      TCase x t d bs -> do
        v <- lookupVar x
        let (lets, u) = letView v
        case u of                          -- TODO: also for literals
          _ | Just (c, as) <- conView u -> simpl $ matchCon lets c as d bs
          TCase y t1 d1 bs1 -> simpl $ mkLets lets $ TCase y t1 d1 $
                                       map (distrCase case1) bs1
            where
              -- Γ x Δ -> Γ x Δ Θ y, where x maps to y and Θ are the lets
              n     = length lets
              rho   = liftS (x + n + 1) (raiseS 1)    `composeS`
                      singletonS (x + n + 1) (TVar 0) `composeS`
                      raiseS (n + 1)
              case1 = applySubst rho (TCase x t d bs)

              distrCase v (TACon c a b) = TACon c a $ TLet b $ raiseFrom 1 a v
              distrCase v (TALit l b)   = TALit l   $ TLet b v
              distrCase v (TAGuard g b) = TAGuard g $ TLet b v
          _ -> do
            d  <- simpl d
            bs <- traverse simplAlt bs
            tCase x t d bs

      TUnit          -> pure t
      TSort          -> pure t
      TErased        -> pure t
      TError{}       -> pure t

    conView (TCon c)           = Just (c, [])
    conView (TApp (TCon c) as) = Just (c, as)
    conView e                  = Nothing

    letView (TLet e b) = first (e :) $ letView b
    letView e          = ([], e)

    mkLets es b = foldr TLet b es

    matchCon _ _ _ d [] = d
    matchCon lets c as d (TALit{}   : bs) = matchCon lets c as d bs
    matchCon lets c as d (TAGuard{} : bs) = matchCon lets c as d bs
    matchCon lets c as d (TACon c' a b : bs)
      | length as /= a = __IMPOSSIBLE__
      | c == c'        = flip (foldr TLet) lets $ mkLet 0 as (raiseFrom a (length lets) b)
      | otherwise      = matchCon lets c as d bs
      where
        mkLet _ []       b = b
        mkLet i (a : as) b = TLet (raise i a) $ mkLet (i + 1) as b

    simplPrim :: TTerm -> Maybe TTerm
    simplPrim u
      | Just (op,  k, v) <- constArithView u,
        Just (op1, j, v) <- constArithView v = pure $ arithFusion k op j op1 v
    simplPrim _ = Nothing

    arithFusion k PAdd j PAdd v = tPlusK (k + j) v
    arithFusion k PAdd j PSub v = tOp PSub (tInt (k + j)) v
    arithFusion k PSub j PAdd v = tOp PSub (tInt (k - j)) v
    arithFusion k PSub j PSub v = tPlusK (k - j) v
    arithFusion _ _ _ _ _ = __IMPOSSIBLE__

    constArithView :: TTerm -> Maybe (TPrim, Integer, TTerm)
    constArithView (TApp (TPrim op) [TLit (LitNat _ k), u])
      | elem op [PAdd, PSub] = Just (op, k, u)
    constArithView (TApp (TPrim op) [u, TLit (LitNat _ k)])
      | op == PAdd = Just (op, k, u)
      | op == PSub = Just (PAdd, -k, u)
    constArithView _ = Nothing

    simplAlt (TACon c a b) = TACon c a <$> underLams a (simpl b)
    simplAlt (TALit l b)   = TALit l   <$> simpl b
    simplAlt (TAGuard g b) = TAGuard   <$> simpl g <*> simpl b

    tCase :: Int -> CaseType -> TTerm -> [TAlt] -> S TTerm
    tCase x t d bs
      | isUnreachable d =
        case reverse bs' of
          [] -> pure d
          TALit _ b   : as  -> pure $ tCase' x t b (reverse as)
          TAGuard _ b : as  -> pure $ tCase' x t b (reverse as)
          TACon c a b : _   -> pure $ tCase' x t d bs'
      | otherwise = pure $ TCase x t d bs'
      where
        bs' = filter (not . isUnreachable) bs

        tCase' x t d [] = d
        tCase' x t d bs = TCase x t d bs

    tApp :: TTerm -> [TTerm] -> S TTerm
    tApp (TLet e b) es = TLet e <$> underLet e (tApp b (raise 1 es))
    tApp (TCase x t d bs) es = do
      d  <- tApp d es
      bs <- mapM (`tAppAlt` es) bs
      simpl $ TCase x t d bs    -- will resimplify branches
    tApp (TVar x) es = do
      v <- lookupVar x
      case v of
        _ | v /= TVar x && isAtomic v -> tApp v es
        TLam{} -> tApp v es   -- could blow up the code
        _      -> pure $ mkTApp (TVar x) es
    tApp f [] = pure f
    tApp (TLam b) (TVar i : es) = tApp (subst 0 (TVar i) b) es
    tApp (TLam b) (e : es) = tApp (TLet e b) es
    tApp f es = pure $ TApp f es

    tAppAlt (TACon c a b) es = TACon c a <$> underLams a (tApp b (raise a es))
    tAppAlt (TALit l b) es   = TALit l   <$> tApp b es
    tAppAlt (TAGuard g b) es = TAGuard g <$> tApp b es

    isAtomic v = case v of
      TVar{}    -> True
      TCon{}    -> True
      TPrim{}   -> True
      TDef{}    -> True
      TLit{}    -> True
      TSort{}   -> True
      TErased{} -> True
      TError{}  -> True
      _         -> False

