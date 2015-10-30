{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
module Agda.Compiler.Treeless.Simplify (simplifyTTerm) where

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

      TApp (TDef f) [TLit (LitNat _ 0), m, n, m']
        | m == m', Just f == divAux -> simpl $ tOp PDiv n (tPlusK 1 m)
        | m == m', Just f == modAux -> simpl $ tOp PMod n (tPlusK 1 m)

      TVar{}         -> pure t
      TDef{}         -> pure t
      TPrim{}        -> pure t
      TApp (TPrim op) args -> do
        args <- mapM simpl args
        let inline (TVar x) = lookupVar x
            inline u        = pure u
        inlined <- mapM inline args
        let nosimpl = TApp (TPrim op) args
        pure $ fromMaybe nosimpl $ simplPrim $ TApp (TPrim op) inlined

      TApp f es      -> TApp <$> simpl f <*> traverse simpl es
      TLam b         -> TLam <$> underLam (simpl b)
      TLit{}         -> pure t
      TCon{}         -> pure t
      TLet e b       -> do
        e <- simpl e
        TLet e <$> underLet e (simpl b)

      TCase x t d bs -> do
        d  <- simpl d
        bs <- traverse simplAlt bs
        tCase x t d bs

      TUnit          -> pure t
      TSort          -> pure t
      TErased        -> pure t
      TError{}       -> pure t

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

