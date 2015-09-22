-- Also works for parts of operators.
module NotInScope where

postulate
  X : Set
  if_then_else_ : X -> X -> X -> X
  x : X

bad = if x thenn x else x

