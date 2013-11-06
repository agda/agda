
module Issue892b where

record R : Set₁ where
  field A : Set
        B : A → Set

-- The type of R.B should print as (r : R) → R.A r → Set
-- rather than ( : R) → R.A  → Set.
bad : R.B
bad = ?

