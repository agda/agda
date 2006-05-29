
module loop where


data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixr 15 ::

data List (A:Set) : Set where
  nil : List A
  (::) : A -> List A -> List A

rev : List _ -> List _ -> List _
rev  nil    ys = ys
rev (x::xs) ys = rev xs (x::ys)

reverse : List Nat -> List Nat
reverse xs = rev xs nil

