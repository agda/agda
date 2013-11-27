-- There was a bug where Confuse and confusing were considered
-- projection-like even though they have absurd clauses.
module _ (A : Set) where

data D : Set where
  d : D

data P : D → Set where

Confuse : (d : D) (p : P d) → Set
Confuse x ()

confusing : (d : D) (p : P d) → Confuse d p
confusing x ()

test : (x : P d) → Set
test x with confusing d x
test x | e = A
