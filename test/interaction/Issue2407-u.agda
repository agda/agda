-- {-# OPTIONS -v tc.cover:20 #-}

-- Andreas, 2017-01-18, issue #2407

-- If underscores are not preserved (issue #819),
-- the case split fails due to size constraints.

open import Common.Size

data D (i : Size) : (j : Size< ↑ i) → Set where

  c : ∀ (j : Size< ↑ i) (k : Size< ↑ j)
       → D i j
       → D j k
       → D i k

split-u : ∀ i (j : Size< ↑ i) → D i j → Set
split-u _ _ x = {!x!}  -- split on x

-- Expected: splitting on x succeeds with
--   split-u _ _ (c j k x x₁) = {!!}
