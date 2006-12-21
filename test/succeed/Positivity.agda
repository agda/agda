
module Bad where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

data Tree : Set where
  node : List Tree -> Tree

data Loop (A : Set) : Set where
  loop : Loop (Loop A) -> Loop A

F : Set -> Set
F A = A

data Ok : Set where
  ok : F Ok -> Ok

