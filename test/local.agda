
module local where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixr 15 ::

data List (A:Set) : Set where
  nil : List A
  (::) : A -> List A -> List A

postulate
  xs : List Nat

reverse : {A:Set} -> List A -> List A
reverse xs = rev xs nil
  where
    rev : _ -> _ -> _
    rev  nil	ys = ys
    rev (x::xs) ys = rev xs (x::ys)

