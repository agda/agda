
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.List

_++_ : List Nat → List Nat → List Nat
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

sum : List Nat → Nat
sum [] = 0
sum (x ∷ xs) = x + sum xs

postulate
  sum-++ : ∀ xs ys → sum (xs ++ ys) ≡ sum xs + sum ys

_ : sum ([] ++ []) ≡ 0
_ = sum-++ {!!} []
