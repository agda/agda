-- Andreas, 2019-09-10, issue #4065, reported by nad

-- If the set of filtered unsolved constraints is empty, Agda
-- should print at least something like "Unsolved constraints"

postulate
  A : Set

record R (F : A → Set) : Set where

module M (r : (F : A → Set) → R F) where

  module T (F : _) = R (r (λ ℓ → F ℓ))

-- WAS (master after 2.6.0):
-- <no error> when checking the module application ...

-- Expected:
-- Unsolved constraints when checking the module application ...
