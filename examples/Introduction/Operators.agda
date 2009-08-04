
-- This module introduces operators.

module Introduction.Operators where

-- Agda has a very flexible mechanism for defining operators, supporting infix,
-- prefix, postfix and mixfix operators.

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- Any name containing underscores (_) can be used as an operator by writing
-- the arguments where the underscores are. For instance, the function _+_ is
-- the infix addition function. This function can be used either as a normal
-- function: '_+_ zero zero', or as an operator: 'zero + zero'.

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

-- A fixity declaration specifies precedence level (50 in this case) and
-- associativity (left associative here) of an operator. Only infix operators
-- (whose names start and end with _) have associativity.
infixl 50 _+_

-- The only restriction on where _ can appear in a name is that there cannot be
-- two underscores in sequence. For instance, we can define an if-then-else
-- operator:

data Bool : Set where
  false : Bool
  true  : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

-- if_then_else_ is treated as a prefix operator (ends, but doesn't begin with
-- an _), so the declared precedence determines how something in an else branch
-- should be parsed. For instance, with the given precedences
--   if x then y else a + b
-- is parsed as
--   if x then y else (a + b)
-- and not
--   (if x then y else a) + b

infix 10 if_then_else_

-- In Agda there is no restriction on what characters are allowed to appear in
-- an operator (as opposed to a function symbol). For instance, it is allowed
-- (but not recommended) to define 'f' to be an infix operator and '+' to be a
-- function symbol.

module BadIdea where

  _f_ : Nat -> Nat -> Nat
  zero  f zero  = zero
  zero  f suc n = suc n
  suc n f zero  = suc n
  suc n f suc m = suc (n f m)

  + : Nat -> Nat
  + n = suc n

