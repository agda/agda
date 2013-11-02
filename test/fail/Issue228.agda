
module Issue228 where

open import Common.Level

postulate
  ∞ : Level

data _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  _,_ : A → B → A × B

data Large : Set ∞ where
  large : Large

data Small : Set₁ where
  small : Set → Small

P : Set
P = Large × Small

[_] : Set → P
[ A ] = (large , small A)

potentially-bad : P
potentially-bad = [ P ]
