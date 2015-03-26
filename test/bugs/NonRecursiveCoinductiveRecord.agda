-- Andreas, 2014-04-23 test case by Andrea Vezzosi
{-# OPTIONS --sized-types --copatterns #-}
-- {-# OPTIONS --show-implicit -v term:60 #-}
module _ where

open import Common.Size

-- Invalid coinductive record, since not recursive.
record ▸ (A : Size → Set) (i : Size) : Set where
  coinductive         -- This should be an error, since non-recursive.
  constructor delay_
  field
    force : ∀ {j : Size< i} → A j

open ▸

-- This fixed-point combinator should not pass the termination checker.
∞fix : ∀ {A : Size → Set} → (∀ {i} → ▸ A i → A i) → ∀ {i} → ▸ A i
force (∞fix {A} f {i}) {j} = f {j} (∞fix {A} f {j})

-- The following fixed-point combinator is not strongly normalizing!
fix : ∀ {A : Size → Set} → (∀ {i} → (∀ {j : Size< i} → A j) → A i) → ∀ {i} {j : Size< i} → A j
fix f = force (∞fix (λ {i} x → f {i} (force x)))

-- test = fix {!!}
-- C-c C-n test gives me a stack overflow
