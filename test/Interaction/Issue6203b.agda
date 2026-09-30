{-# OPTIONS --cubical #-}
module Issue6203b where

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

-- need a confounding instance otherwise Agda will eagerly commit to hl
postulate instance H-Level-⊤ : ∀ {n} → H-Level Nat n

-- hlevel is projection-like: elaborate-and-give will reduce it before
-- printing. Previously, elaborate-and-give would result in "hlevel _",
-- which fails on reload (instance selection can't decide on the hl
-- instance without the "2" argument).
-- Should result in: H-Level.has-hlevel x
private module _ {ℓ} {A : Type ℓ} ⦃ hl : H-Level A 2 ⦄ where
  p : is-hlevel A 2
  p = {! hlevel 2 !}
