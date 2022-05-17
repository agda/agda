-- Andreas, 2014-01-21, Issue 1209 reported by Andrea

{-# OPTIONS --cubical-compatible #-}
{-# OPTIONS --copatterns #-}
{-# OPTIONS --sized-types #-}

open import Common.Size

record R (i : Size) : Set where
  coinductive
  field
    force : (j : Size< i) → R j

postulate
  f : ∀ {i} → R i → R i

t : (i : Size) → R i
R.force (t i) j = f (t j)

-- should termination check
