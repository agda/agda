-- Andreas, 2016-12-09, issue #2331
-- Testcase from Nisse's application

open import Common.Size

data D (i : Size) : Set where
  c : (j : Size< i) → D i

postulate
  f : (i : Size) → ((j : Size< i) → D j → Set) → Set

module Mutual where
  mutual
    test : (i : Size) → D i → Set
    test  i (c j) = f j (helper i j)

    helper : (i : Size) (j : Size< i) (k : Size< j) → D k → Set
    helper i j k = test k

module Where where
  test : (i : Size) → D i → Set
  test i (c j) = f j helper
    where
    helper : (k : Size< j) → D k → Set
    helper k = test k

-- While k is an unusable size per se, in combination with the usable size j
-- (which comes from a inductive pattern match)
-- it should be fine to certify termination.
