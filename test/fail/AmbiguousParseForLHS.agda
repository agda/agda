-- Occurs there are several ways to parse a left-hand side.
module AmbiguousParseForLHS where

infix 0 if_then_else_ if_then_

data X : Set where
  if_then_else_ : X -> X -> X -> X
  if_then_      : X -> X -> X
  x             : X

bad : X -> X
bad (if x then if x then x else x) = x
bad _                              = if x then x
