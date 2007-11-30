
module ModuleInstInLet where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

module List (Elem : Set) where

  data List : Set where
    []   : List
    _::_ : Elem -> List -> List

xs : let open List Nat
     in  List
xs = List._::_ zero List.[]

