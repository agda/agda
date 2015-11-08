-- Andreas, 2013-10-20 'with' only abstracts at base type
module WithOfFunctionType where

postulate
  A B : Set
  P : B → Set
  mkP : (x : B) → P x
  f : A → B
  a : A

test : P (f a)
test with f
... | g = mkP (g a)

