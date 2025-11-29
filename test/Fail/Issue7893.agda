{-# OPTIONS --rewriting --local-confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.List
open import Agda.Builtin.Nat

private variable
  A : Set
  x : A
  m n : Nat

_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

replicate : Nat → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

postulate
  replicate-rew : replicate (m + n) x ≡ replicate m x ++ replicate n x
  plus-zero : m + 0 ≡ m

{-# REWRITE replicate-rew #-}
{-# REWRITE plus-zero #-}
