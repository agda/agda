
module UnequalHiding where

data One : Set where one : One

f : ({A : Set} -> A -> A) -> One
f = \(id : (A : Set) -> A -> A) -> id One one
