
module list where

module List (A : Set) where

  data List : Set where
    nil  : List
    _::_ : A -> List -> List

  _++_ : List -> List -> List
  nil       ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

