
module Lib.List where

infixr 40 _::_ _++_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
