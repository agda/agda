{-# OPTIONS --inversion-max-depth=10 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data ⊥ : Set where

double : Nat → Nat
double zero    = zero
double (suc n) = suc (suc (double n))

postulate
  doubleSuc : (x y : Nat) → double x ≡ suc (double y) → ⊥

diverge : ⊥
diverge = doubleSuc _ _ refl

{-
  double ?x == suc (double ?y)
    ?x := suc ?x₁
  suc (suc (double ?x₁)) == suc (double ?y)
  suc (double ?x₁) == double ?y
    ?y := suc ?y₁
  double ?x₁ == suc (double ?y₁)
  .
  .
  .
-}
