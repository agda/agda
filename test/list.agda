
module T where

module List (A:Set) where

  data List : Set where
    nil  : List
    (::) : A -> List -> List

  (++) : List -> List -> List
  nil	  ++ ys = ys
  (x::xs) ++ ys = x :: (xs ++ ys)

