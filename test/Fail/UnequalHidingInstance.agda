module UnequalHidingInstance where

postulate
  A : Set
  B : A -> Set
  x : A
  y : B x

f : ({{ x : A }} -> B x -> B x) -> B x
f = \(id : (x : A) -> B x -> B x) -> id x y

