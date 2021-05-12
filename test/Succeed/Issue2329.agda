-- Andreas, 2017-01-20, issue #2329

-- Neutral sizes cannot be used by the size solver,
-- thus, should be handled by coerceSize.

-- {-# OPTIONS -v tc:10 #-}
-- {-# OPTIONS -v tc.conv.coerce:20 #-}
-- {-# OPTIONS -v tc.size:20 #-}
-- {-# OPTIONS -v tc.size.solve:50 #-}

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

record R (i : Size) : Set where
  field
    j : Size< i

postulate
  f : ∀ i → R i

works : ∀ i → R i
R.j (works i) = R.j {i} (f i)

test : ∀ i → R i
R.j (test i) = R.j (f i)

-- Error WAS:
-- Unsolved constraint:
-- ↑ R.j (f i) =< i : Size
