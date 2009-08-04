-- Occurs there are several ways to parse a left-hand side.
module AmbiguousParseForLHS where

data X : Set where
  if_then_else_ : X -> X -> X -> X
  if_then_      : X -> X -> X
  x             : X

bad : X -> X
bad (if x then if x then x else x) = x
bad _                              = if x then x
