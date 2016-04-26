-- Andreas, AIM XXIII, 2016-04-26 flight EDI-GOT home

-- {-# OPTIONS -v impossible:10 #-}

-- Parameter arguments of overloaded projection applications
-- should not be skipped!

record R A : Set where
  field f : A
open R

record S A : Set where
  field f : A
open S

module _ (A B : Set) (a : A) where

  r : R A
  f r = a

  test1 = f {A = A} r
  test2 = f {A} r

  -- test3 = f {{A}} r
  test = f {{A = A}} r
