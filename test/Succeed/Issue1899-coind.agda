-- Andreas, 2017-01-13, regression introduced by the fix of #1899
-- test case and report by Nisse

-- {-# OPTIONS -v term:40 #-}
{-# OPTIONS --guardedness --sized-types #-}

open import Agda.Builtin.Size

mutual

  D : Size → Set
  D i = D′ i

  record D′ (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → D j

test : D′ ∞
D′.force test = test

-- Same without sizes (they are not used)

mutual
  E = E'
  record E' : Set where
    coinductive
    field force : E

testE : E'
E'.force testE = testE

-- Both should succeed, no termination errors.
