-- Andreas, 2026-04-30, issue #6770, reported by Orestis Melkonian
-- Alternative reproducer by nad

postulate
  A : Set

variable
  x : A

record R (x : A) : Set₁ where
  field
    B : Set

-- The following code works:

module _ {x} (r : R x) (open R r) where

  _ : Set
  _ = B

-- However, the following code is rejected:

module _ (r : R x) (open R r) where

  _ : Set
  _ = B
