
-- Operator example

module Operators where

data True : Set where
  tt : True

data False : Set where

data Bool : Set where
  false : Bool
  true  : Bool

-- An operator is declared with '_' where the arguments go
if_then_else_ : Bool -> {A : Set} -> A -> A -> A
if true  then x else y = x
if false then x else y = y

-- The actual name of the operator is obtained by removing all the spaces from
-- the declared version.
infix 1 if_then_else_

-- This name can be used in normal applications, for instance, if a hidden argument
-- needs to be supplied.
_&&_ : Bool -> Bool -> Bool
x && y = if_then_else_ x {Bool} y false

-- Operators can be prefix...
¬_ : Bool -> Bool
¬ true  = false
¬ false = true

-- ...or postfix...
_valid : Bool -> Set
true  valid = True
false valid = False

-- ...or roundfix
⟦_⟧ : Bool -> Set
⟦ x ⟧ = x valid

