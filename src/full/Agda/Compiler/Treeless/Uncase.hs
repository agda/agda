module Agda.Compiler.Treeless.Uncase (caseToSeq) where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst
import Agda.Compiler.Treeless.Compare

import Agda.Utils.Impossible

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
  TCoerce t -> TCoerce (uncase t)
  where
    uncaseAlt (TACon c a b) = TACon c a $ uncase b
    uncaseAlt (TALit l b)   = TALit l $ uncase b
    uncaseAlt (TAGuard g b) = TAGuard (uncase g) (uncase b)

    doCase x t d bs
      | Just u <- mu,
        all (equalTo x u) bs = maybeSeq u
      | otherwise            = fallback
      where
        maybeSeq u | caseLazy t = u
                   | otherwise  = tApp (TPrim PSeq) [TVar x, u]
        fallback = TCase x t d bs
        (fv, mu)
          | isUnreachable d =
            case last bs of
              TACon _ a b -> (a, tryStrengthen a b)
              TALit l b   -> (0, Just b)
              TAGuard _ b -> (0, Just b)
          | otherwise = (0, Just d)

    equalTo :: Int -> TTerm -> TAlt -> Bool
    equalTo x t (TACon c a b)
      | Just b' <- tryStrengthen a b = equalTerms (subst x v t) (subst x v b')
      | otherwise                    = False
      where v = mkTApp (TCon c) (replicate a TErased)
    equalTo x t (TALit l b)   = equalTerms (subst x (TLit l) t) (subst x (TLit l) b)
    equalTo x t (TAGuard _ b) = equalTerms t b

    tLet e b =
      case occursIn 0 b of
        Occurs 0 _ _ -> strengthen __IMPOSSIBLE__ b
        _            -> TLet e b

    -- Primitive operations are already strict
    tApp (TPrim PSeq) [_, b@(TApp (TPrim op) _)]
      | op `elem` [PAdd, PSub, PMul, PLt, PGeq, PRem, PQuot] || isPrimEq op = b
    tApp f es = TApp f es
