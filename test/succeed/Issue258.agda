
module Issue258 where

data D (A : Set) : Set where
  d : D A

foo : Set → Set
foo A with d {A}
foo A | p = A
