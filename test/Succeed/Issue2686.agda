-- Andreas, 2017-08-13, issue #2686
-- Overloaded constructor where only one alternative is not abstract.
-- Not ambiguous, since abstract constructors are not in scope!

-- {-# OPTIONS -v tc.check.term:40 #-}

abstract
  data A : Set where
    c : A

data D : Set where
  c : D

test = c

match : D → D
match c = c
