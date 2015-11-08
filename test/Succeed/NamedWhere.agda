
module NamedWhere where

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

reverse : {A : Set} -> List A -> List A
reverse {A} xs = rev xs []
  module reverse where
    rev : List A -> List A -> List A
    rev []        ys = ys
    rev (x :: xs) ys = rev xs (x :: ys)

rev : {A : Set} -> List A -> List A -> List A
rev = reverse.rev []

