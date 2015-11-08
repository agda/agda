{-# LANGUAGE PatternGuards #-}
module Agda.Compiler.Treeless.Uncase (caseToSeq) where

import Control.Applicative

import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Compare

caseToSeq :: Monad m => TTerm -> m TTerm
caseToSeq t = return $ uncase t

uncase :: TTerm -> TTerm
uncase t = case t of
  TVar{}    -> t
  TPrim{}   -> t
  TDef{}    -> t
  TApp f es -> TApp (uncase f) (map uncase es)
  TLam b    -> TLam $ uncase b
  TLit{}    -> t
  TCon{}    -> t
  TLet e b  -> TLet (uncase e) (uncase b)
  TCase x t d bs -> doCase x t (uncase d) (map uncaseAlt bs)
  TUnit{}   -> t
  TSort{}   -> t
  TErased{} -> t
  TError{}  -> t
  where
    uncaseAlt (TACon c a b) = TACon c a $ uncase b
    uncaseAlt (TALit l b)   = TALit l $ uncase b
    uncaseAlt (TAGuard g b) = TAGuard (uncase g) (uncase b)

    doCase x t d bs
      | fv > 0               = fallback   -- can't do it for constructors with arguments
      | all (equalTo x u) bs = tOp PSeq (TVar x) u
      | otherwise            = fallback
      where
        fallback = TCase x t d bs
        (fv, u)
          | isUnreachable d =
            case last bs of
              TACon _ a b -> (a, b)
              TALit l b   -> (0, b)
              TAGuard _ b -> (0, b)
          | otherwise = (0, d)

    equalTo :: Int -> TTerm -> TAlt -> Bool
    equalTo x t (TACon c a b) = a == 0 && equalTerms (subst x (TCon c) t) (subst x (TCon c) b)
    equalTo x t (TALit l b)   = equalTerms (subst x (TLit l) t) (subst x (TLit l) b)
    equalTo x t (TAGuard _ b) = equalTerms t b

