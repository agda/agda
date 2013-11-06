
module Issue892a where

record R : Set₁ where
  field f : Set
  g : Set
  g = f

-- The type of R.g should print as (r : R) → Set
-- rather than ( : R) → Set.
bad : R.g
bad = ?

