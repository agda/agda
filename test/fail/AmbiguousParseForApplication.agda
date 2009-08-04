-- Occurs there are several ways to parse an operator application.
module AmbiguousParseForApplication where

postulate
  X             : Set
  if_then_else_ : X -> X -> X -> X
  if_then_      : X -> X -> X

bad : X -> X
bad x = if x then if x then x else x

