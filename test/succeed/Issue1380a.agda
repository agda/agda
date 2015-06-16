{-# OPTIONS --exact-split #-}
-- {-# OPTIONS -v tc.cover:10 #-}

postulate
  A : Set

record I : Set where
  constructor i
  field
    f : A

data Wrap : (j : I) → Set where
  con : (j : I) → Wrap j

postulate
  C : Set
  anything : C

test : (X : I) -> Wrap X -> C
test (i ._) (con x) = anything
