{-# LANGUAGE RecordWildCards, PatternGuards #-}
module Agda.Compiler.Treeless.Simplify (simplifyTTerm) where

import Agda.Syntax.Treeless
import Agda.Syntax.Internal (Substitution'(..))
import Agda.Syntax.Literal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.Utils.Maybe

import Agda.Compiler.Treeless.Subst

data FunctionKit = FunctionKit
  { modAux, divAux :: Maybe QName }

simplifyTTerm :: TTerm -> TCM TTerm
simplifyTTerm t = do
  modAux <- getBuiltinName builtinNatModSucAux
  divAux <- getBuiltinName builtinNatDivSucAux
  return $ if isNothing modAux && isNothing divAux then t else
    simplify FunctionKit{ modAux = modAux, divAux = divAux } t

simplify :: FunctionKit -> TTerm -> TTerm
simplify FunctionKit{..} = simpl
  where
    simpl t = case t of

      TApp (TDef f) [TLit (LitInt _ 0), m, n, m']
        | m == m', Just f == divAux -> TApp (TPrim "div") [n, TPlus 1 m]
        | m == m', Just f == modAux -> TApp (TPrim "mod") [n, TPlus 1 m]

      TVar{}         -> t
      TDef{}         -> t
      TPrim{}        -> t
      TApp f es      -> TApp (simpl f) $ map simpl es
      TLam b         -> TLam (simpl b)
      TLit{}         -> t
      TPlus k n      -> TPlus k (simpl n)
      TCon{}         -> t
      TLet e b       -> TLet (simpl e) (simpl b)

      TCase x t d bs -> tCase x t (simpl d) (map simplAlt bs)

      TPi a b        -> TPi (simplTy a) (simplTy b)
      TUnit          -> t
      TSort          -> t
      TErased        -> t
      TError{}       -> t

    simplAlt (TACon c a b) = TACon c a (simpl b)
    simplAlt (TALit l b)   = TALit l (simpl b)
    simplAlt (TAPlus k b)  = TAPlus k (simpl b)

    simplTy (TType t) = TType (simpl t)

tCase :: Int -> CaseType -> TTerm -> [TAlt] -> TTerm
tCase x t d bs
  | isError d =
    case reverse bs' of
      [] -> d
      TALit _ b   : as  -> tCase' x t b (reverse as)
      TAPlus k b  : as  -> tCase' x t (TLet (TApp (TPrim "-") [TVar x, tInt k]) b) (reverse as)
      TACon c a b : _   -> tCase' x t d bs'
  | otherwise = TCase x t d bs'
  where
    bs' = filter (not . isErrorAlt) bs

    tCase' x t d [] = d
    tCase' x t d bs = TCase x t d bs

isErrorAlt :: TAlt -> Bool
isErrorAlt = isError . aBody

isError :: TTerm -> Bool
isError TError{} = True
isError _ = False
