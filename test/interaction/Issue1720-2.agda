-- Andreas, 2016-07-29, issue #1720 reported by Mietek Bak

{-# OPTIONS --double-check #-}

postulate
  A  : Set
  B  : A → Set
  a0 : A
  b0 : B a0

record R (a1 : A) (b1 : B a1) : Set where

  field fa : A

  a : A
  a = {!a1!}

  field fb : B fa

  b : B {!!}
  b = {!b1!}

  field f : A

-- Problem:
-- Interaction points are doubled.
