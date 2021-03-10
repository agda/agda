-- Andreas, 2020-02-15, issue #4447
--
-- Positivity checker needs to see the constructor types
-- in the same way as the type checker has seen them.
--
-- Thus, we need to reduce types of constructors even
-- with definitions that have not yet been subjected to termination
-- checking, e.g. because they live in a mutual block with the data type.

-- {-# OPTIONS -v term:10 #-}
-- {-# OPTIONS -v tc.pos:10 #-}
-- {-# OPTIONS -v tc.data:10 #-}

data ⊥ : Set where

-- Mutual block:

data D : Set
D' = (D → ⊥) → D
data D where
  abs : D'

-- Positivity checker needs to unfold D', otherwise it does not see
-- the correct occurrences of D.

-- From here, the road to absurdity is paved:

app : D → D → ⊥
app (abs f) = f

delta : D → ⊥
delta x = app x x

Omega : ⊥
Omega = delta (abs delta)
