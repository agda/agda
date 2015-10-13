{-# LANGUAGE RecordWildCards, PatternGuards #-}
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

      TApp (TDef f) [TLit (LitInt _ 0), m, n, m']
        | m == m', Just f == divAux -> simpl $ tOp PDiv n (tPlusK 1 m)
        | m == m', Just f == modAux -> simpl $ tOp PMod n (tPlusK 1 m)

      TVar{}         -> pure t
      TDef{}         -> pure t
      TPrim{}        -> pure t
      t@TApp{} | Just (k, n) <- plusKView t -> do
        n <- simpl n
        case n of
          TVar x -> do
            u <- lookupVar x
            case u of
              TApp (TPrim PSub) [TVar y, TLit (LitInt _ j)]
                | k == j    -> pure $ TVar y
                | k > j     -> pure $ tPlusK (k - j) (TVar y)
                | otherwise -> pure $ tOp PSub (TVar y) (tInt (j - k))
              _ -> pure $ tPlusK k n
          _ -> pure $ tPlusK k n
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

    simplAlt (TACon c a b) = TACon c a <$> underLams a (simpl b)
    simplAlt (TALit l b)   = TALit l   <$> simpl b
    simplAlt (TAPlus k b)  = TAPlus k  <$> underLam (simpl b)

    tCase :: Int -> CaseType -> TTerm -> [TAlt] -> S TTerm
    tCase x t d bs
      | isUnreachable d =
        case reverse bs' of
          [] -> pure d
          TALit _ b   : as  -> pure $ tCase' x t b (reverse as)
          TAPlus k b  : as  -> do
                 -- TODO: retraversing the body (quadratic in nesting level!)
            b <- simpl (TLet (tOp PSub (TVar x) (tInt k)) b)
            pure $ tCase' x t b (reverse as)
          TACon c a b : _   -> pure $ tCase' x t d bs'
      | otherwise = pure $ TCase x t d bs'
      where
        bs' = filter (not . isUnreachable) bs

        tCase' x t d [] = d
        tCase' x t d bs = TCase x t d bs

