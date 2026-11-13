module Issue6962Expression where

postulate
  f : Set → Set

-- Typed binders belong to declaration heads, not ordinary applications.
bad = f (A : Set)
