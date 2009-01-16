module DependentPatternMatchingOnCodata where

codata C : Set where
  c : C

data D : C → Set where
  d : D c

f : (x : C) → D x
f c = d
