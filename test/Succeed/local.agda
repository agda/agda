
module local where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixr 15 _::_

data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

reverse : {A : Set} -> List A -> List A
reverse {A} xs = rev xs nil
  where
    rev : List A -> List A -> List A
    rev  nil      ys = ys
    rev (x :: xs) ys = rev xs (x :: ys)

postulate
  xs : List Nat

