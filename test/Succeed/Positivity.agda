
module Positivity where

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

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

data PList (A : Set) : Set where
  leaf : A -> PList A
  succ : PList (A × A) -> PList A

data Bush (A : Set) : Set where
  nil  : Bush A
  cons : A -> Bush (Bush A) -> Bush A

F : Set -> Set
F A = A

data Ok : Set where
  ok : F Ok -> Ok

