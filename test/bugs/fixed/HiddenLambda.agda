
module HiddenLambda where

postulate
  A : Set
  T : A -> Set

H : Set
H = {x : A} -> T x -> T x

-- H doesn't reduce when checking the body of h
h : H
h = \tx -> tx

