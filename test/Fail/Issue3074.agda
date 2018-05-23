
module _ where

postulate
  A : Set

data Box : Set where
  box : A → Box

unbox : Box → A
unbox (box {x}) = x
