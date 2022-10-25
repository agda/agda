{-# OPTIONS --cubical #-}
module Issue6203a where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Nat
open import Agda.Builtin.Cubical.Path

is-hlevel : ∀ {ℓ} → Type ℓ → Nat → Type ℓ
is-hlevel A 0 = (x y : A) → x ≡ y
is-hlevel A (suc n) = (x y : A) → is-hlevel (x ≡ y) n

record H-Level {ℓ} (T : Type ℓ) (n : Nat) : Type ℓ where
  constructor hlevel-instance
  field
    has-hlevel : is-hlevel T n

hlevel : ∀ {ℓ} {T : Type ℓ} n ⦃ x : H-Level T n ⦄ → is-hlevel T n
hlevel n ⦃ x ⦄ = H-Level.has-hlevel x
{-# NOT_PROJECTION_LIKE hlevel #-}

-- hlevel is not projection-like: elaborate-and-give will insert it
-- as-is. previously, elaborate-and-give would result in "hlevel _",
-- which fails on reload.
-- Should result in: hlevel 2.
private module _ {ℓ} {A : Type ℓ} ⦃ hl : H-Level A 2 ⦄ where
  p : is-hlevel A 2
  p = {! hlevel 2 !}
