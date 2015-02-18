
module Bool where

data Bool : Set where
  true  : Bool
  false : Bool

infix 0 if_then_else_

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y
