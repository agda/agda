{-# OPTIONS --cubical #-}
module _ where
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Bool

data S¹ : Set where
  base : S¹
  loop : base ≡ base

-- We cannot allow this definition as
--   decideEq (loop i)  base ↦ false
-- but
--   decideEq (loop i0) base ↦ true

decideEq : ∀ (x y : S¹) → Bool
decideEq base     base     = true
decideEq (loop i) (loop j) = true
decideEq x        y        = false
