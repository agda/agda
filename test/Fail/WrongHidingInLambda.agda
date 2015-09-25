
module WrongHidingInLambda where

f : (A : Set) -> A -> A
f = \{A} x -> x

