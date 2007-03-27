
module MetaOccursInItself where

data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

data One : Set where one : One

postulate
  f : (A : Set) -> (A -> List A) -> One

err : One
err = f _ (\x -> x)

