{-# OPTIONS --hidden-argument-puns #-}

open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

record R : Set where
  constructor c
  field
    {m}  : Nat
    {xs} : Vec Nat 1
    n    : Nat
    ys   : Vec Nat 1

data Unit : Set where
  unit : Unit

f₁ : Unit → R → R
f₁ unit x = x

f₂ : Unit → R → R
f₂ unit x = x

{-# DISPLAY f₁ _ (c {xs}   n ys) = c n  xs #-}
{-# DISPLAY f₂ _ (c {(xs)} n ys) = c xs ys #-}

r : R
r = c {m = zero} {xs = zero ∷ []} (suc zero) (suc zero ∷ [])

r₁ : Unit → R
r₁ x = f₁ x r

r₂ : Unit → R
r₂ x = f₂ x r
