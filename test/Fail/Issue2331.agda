-- Andreas, 2017-07-26, issue #2331.
-- Andrea found a counterexample against the "usable decrease" feature:

open import Agda.Builtin.Size

data D (i : Size) : Set where
  c : (j : Size< i) → D i

mutual
  test : (i : Size) → D i → Set
  test  i (c j) = (k : Size< j) (l : Size< k) → helper i j k (c l)

  helper : (i : Size) (j : Size< i) (k : Size< j) → D k → Set
  helper i j k d = test k d

-- Should not termination check.
