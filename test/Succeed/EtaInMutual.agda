-- Andreas, 2016-09-20 issue #2197
-- We are now only turning eta-equality on after positivity check.
-- This is at the end of the mutual block.

module _ where

open import Common.Equality

module Works where

  mutual

    record ⊤ : Set where
      eta-equality

    test : ∀ {x y : ⊤} → x ≡ y
    test = refl

mutual

  record ⊤ : Set where

  test : ∀ {x y : ⊤} → x ≡ y
  test = refl
    -- Fails, as eta-equality is only turned on after mutual block.
