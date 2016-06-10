{-# LANGUAGE CPP #-}
module Agda.Compiler.Treeless.Uncase (caseToSeq) where

import Control.Applicative
import Data.Monoid

import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Compare

import Agda.Utils.Impossible
#include "undefined.h"

caseToSeq :: Monad m => TTerm -> m TTerm
caseToSeq t = return $ uncase t

uncase :: TTerm -> TTerm
uncase t = case t of
  TVar{}    -> t
  TPrim{}   -> t
  TDef{}    -> t
  TApp f es -> tApp (uncase f) (map uncase es)
  TLam b    -> TLam $ uncase b
  TLit{}    -> t
  TCon{}    -> t
  TLet e b  -> tLet (uncase e) (uncase b)
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
      | all (equalTo x u) bs = tApp (TPrim PSeq) [TVar x, u]
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

    -- There's no sense binding an expression just to seq on it.
    tLet e b =
      case occursIn 0 b of
        Occurs 0 _ _                   -> strengthen __IMPOSSIBLE__ b
        Occurs _ _ (SeqArg (All True)) -> subst 0 TErased b -- this will get rid of the seq
        _                              -> TLet e b

    -- Primitive operations are already strict
    tApp (TPrim PSeq) [_, b@(TApp (TPrim op) _)]
      | op `elem` [PAdd, PSub, PMul, PLt, PEq, PGeq, PRem, PQuot] = b
    tApp f es = TApp f es
