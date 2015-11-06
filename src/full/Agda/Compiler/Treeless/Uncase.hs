{-# LANGUAGE PatternGuards #-}
module Agda.Compiler.Treeless.Uncase (caseToSeq) where

import Control.Applicative

import Agda.Syntax.Treeless
import Agda.Syntax.Literal
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst

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
      | isUnreachable d      = fallback   -- only happens for constructor cases which we ignore anyway
      | all (equalTo x d) bs = tOp PSeq (TVar x) d
      | otherwise            = fallback
      where fallback = TCase x t d bs

    equalTo :: Int -> TTerm -> TAlt -> Bool
    equalTo _ _ TACon{}       = False -- skip constructor cases (don't need to be uncased)
    equalTo x t (TALit l b)   = equalTerms (subst x (TLit l) t) (subst x (TLit l) b)
    equalTo x t (TAGuard _ b) = equalTerms t b

equalTerms :: TTerm -> TTerm -> Bool
equalTerms u v =
  case (evalPrims u, evalPrims v) of
    (TLet s u@(TCase 0 _ _ _), TLet t v@(TCase 0 _ _ _)) ->
      equalTerms s t && equalTerms u v
    (TLet _ (TCase 0 _ _ _), _)      -> False
    (_, TLet _ (TCase 0 _ _ _))      -> False
    (TLet t u, v)                    -> equalTerms (subst 0 t u) v
    (u, TLet t v)                    -> equalTerms u (subst 0 t v)
    (u, v) | u == v                  -> True
    (TApp f us, TApp g vs)           -> eqList equalTerms (f : us) (g : vs)
    (TCase x _ d as, TCase y _ e bs) -> x == y && equalTerms d e && eqList equalAlts as bs
    (TLam u, TLam v)                 -> equalTerms u v
    _                                -> False

equalAlts :: TAlt -> TAlt -> Bool
equalAlts (TACon c a b) (TACon c1 a1 b1) = (c, a) == (c1, a1) && equalTerms b b1
equalAlts (TALit l b)   (TALit l1 b1)    = l == l1 && equalTerms b b1
equalAlts (TAGuard g b) (TAGuard g1 b1)  = equalTerms g g1 && equalTerms b b1
equalAlts _ _ = False

eqList :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqList eq xs ys = length xs == length ys && and (zipWith eq xs ys)

evalPrims :: TTerm -> TTerm
evalPrims (TApp (TPrim op) [a, b])
  | Just n <- intView (evalPrims a),
    Just m <- intView (evalPrims b),
    Just r <- applyPrim op n m = tInt r
evalPrims t = t

applyPrim :: TPrim -> Integer -> Integer -> Maybe Integer
applyPrim PAdd a b = Just (a + b)
applyPrim PSub a b = Just (a - b)
applyPrim PDiv a b | b /= 0    = Just (div a b)
                   | otherwise = Nothing
applyPrim PMod a b | b /= 0    = Just (mod a b)
                   | otherwise = Nothing
applyPrim PGeq _ _ = Nothing
applyPrim PLt  _ _ = Nothing
applyPrim PIf  _ _ = Nothing
applyPrim PSeq _ _ = Nothing

