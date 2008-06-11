
module ForallStyleDataParams where

data List A : Set where
  [] : List A
  _::_ : A -> List A -> List A
