module Issue1290b where

open import Issue1290

data Eq (x : R) : R → Set where
  refl : Eq x x

test : Eq x (exp x)
test = refl
