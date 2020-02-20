module Agda.Compiler.Treeless.Compare (equalTerms) where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Substitute
import Agda.Compiler.Treeless.Subst () --instance only

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
applyPrim PMul a b = Just (a * b)
applyPrim PQuot a b | b /= 0    = Just (quot a b)
                   | otherwise = Nothing
applyPrim PRem a b | b /= 0    = Just (rem a b)
                   | otherwise = Nothing
applyPrim PGeq _ _ = Nothing
applyPrim PLt  _ _ = Nothing
applyPrim PEqI _ _ = Nothing
applyPrim PEqF _ _ = Nothing
applyPrim PEqC _ _ = Nothing
applyPrim PEqS _ _ = Nothing
applyPrim PEqQ _ _ = Nothing
applyPrim PIf  _ _ = Nothing
applyPrim PSeq _ _ = Nothing
applyPrim PAdd64 _ _ = Nothing
applyPrim PSub64 _ _ = Nothing
applyPrim PMul64 _ _ = Nothing
applyPrim PQuot64 _ _ = Nothing
applyPrim PRem64 _ _ = Nothing
applyPrim PLt64  _ _ = Nothing
applyPrim PEq64 _ _ = Nothing
applyPrim PITo64 _ _ = Nothing
applyPrim P64ToI _ _ = Nothing

