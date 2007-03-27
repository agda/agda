
module WrongHidingInApplication where

id : (A : Set) -> A -> A
id A x = x

foo : (A : Set) -> A -> A
foo A x = id {A} x

