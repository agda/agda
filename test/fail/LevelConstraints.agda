{-# OPTIONS --universe-polymorphism #-}

-- This test case documents some level constraints that we can't solve
-- either because the solver isn't smart enough or because it's not safe
-- to solve them.

module LevelConstraints where

open import Imports.Level

postulate
  a b     : Level
  OfLvl   : ∀ ℓ → Set ℓ → Set
  SameLvl : ∀ {ℓ} → Set ℓ → Set ℓ → Set

  -- Here we get two constraints by themselves unsolveable constraints:
  --   _18 ⊔ a = _18   (solved by _18 := a ⊔ ℓ, for any ℓ)
  --   a ⊔ _18 = a     (solved by _18 := a  or  _18 := 0)
  -- Taken together the only solution is _18 := a, but we don't look at
  -- more than one constraint at a time.
  bar : (A : Set _)(B : Set a) → SameLvl A (A → B) → SameLvl B (A → B)