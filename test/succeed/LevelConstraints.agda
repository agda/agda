
module LevelConstraints where

open import Common.Level

postulate
  a b     : Level
  OfLvl   : ∀ ℓ → Set ℓ → Set
  SameLvl : ∀ {ℓ} → Set ℓ → Set ℓ → Set

  -- Here we get two constraints by themselves unsolveable constraints:
  --   _18 ⊔ a = _18   (solved by _18 := a ⊔ ℓ, for any ℓ)
  --   a ⊔ _18 = a     (solved by _18 := a  or  _18 := 0)
  -- By looking at both constraints together we can find the unique solution
  --   _18 := a
  bar : (A : Set _)(B : Set a) → SameLvl A (A → B) → SameLvl B (A → B)