data ⊥ : Set where

data Maybe : Set where
  just : ⊥ → Maybe
  nothing : Maybe

test : Set → Set
test x with nothing
test x | just ()
test x | nothing = test x
