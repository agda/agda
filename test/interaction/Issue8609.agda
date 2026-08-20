{-# OPTIONS -v mimer:30 -v mimer.top:0 #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat

sum : List Nat → Nat
sum []       = 0
sum (x ∷ xs) = x + sum xs

data ListSum (n : Nat) : Set where
  listSum : (xs : List Nat) → sum xs ≡ n → ListSum n

test : ListSum 3
test = listSum {!!} refl
