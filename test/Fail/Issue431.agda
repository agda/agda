{-# OPTIONS --inversion-max-depth=2 #-}

-- open import Agda.Builtin.Nat
-- open import Agda.Builtin.Equality

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

postulate
  _≡_ : Nat → Nat → Set
  refl : ∀ {n} → n ≡ n

data ⊥ : Set where

double : Nat → Nat
double zero    = zero
double (suc n) = suc (suc (double n))

postulate
  doubleSuc : (x y : Nat) → double x ≡ suc (double y) → ⊥

diverge : ⊥
diverge = doubleSuc _ _ refl

  -- s s x = s (d y)

  -- s x = db y

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
