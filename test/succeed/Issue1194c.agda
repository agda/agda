-- Andreas, 2014-09-23
-- Syntax declaration for overloaded constructor.

-- {-# OPTIONS -v scope.operators:50 #-}

syntax c x = ⟦ x ⟧

data D1 : Set where
  c : D1

data D2 : Set where
  c : D1 → D2

test : D2
test = ⟦ c ⟧

-- Should work.
