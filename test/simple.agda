
module test.simple where

postulate
  A : Set
  idA : A -> A
  F : Set -> Set
  H : (A,B:Set) -> Prop
  id : (A:Set) -> A -> A

id' = id

