-- Andreas, 2016-07-29, issue #1720 reported by Mietek Bak

postulate
  A B : Set
  a0 : A
  b0 : B

record R (a1 : A) (b1 : B) : Set where

  field fa : A

  a : A
  a = {!!}

  field fb : B

  b : B
  b = {!!}

  field f : A

-- Problem:
-- Interaction points are doubled.
