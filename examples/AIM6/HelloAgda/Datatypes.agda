{-

        Agda Implementors' Meeting VI

                  Göteborg
             May 24 - 30, 2007


                Hello Agda!

                Ulf Norell

-}

-- This is where the fun begins.
-- Unleashing datatypes, pattern matching and recursion.

module Datatypes where

{-

  Simple datatypes.

-}

-- Now which datatype should we start with...?

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- Let's start simple.
pred : Nat -> Nat
pred zero    = zero
pred (suc n) = n

-- Now let's do recursion.
_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

-- An aside on infix operators:
-- Any name containing _ can be used as a mixfix operator.
-- The arguments simply go in place of the _. For instance:

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

-- To declare the associativity and precedence of an operator
-- we write. In this case we need parenthesis around the else branch
-- if its precedence is lower than 10. For the condition and the then
-- branch we only need parenthesis for things like λs.
infix 10 if_then_else_


{-

  Parameterised datatypes

-}

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

infixr 50 _::_

-- The parameters are implicit arguments to the constructors.
nil : (A : Set) -> List A
nil A = [] {A}

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

{-

  Empty datatypes

-}

-- A very useful guy is the empty datatype.
data False : Set where

-- When pattern matching on an element of an empty type, something
-- interesting happens:

elim-False : {A : Set} -> False -> A
elim-False ()  -- Look Ma, no right hand side!

-- The pattern () is called an absurd pattern and matches elements
-- of an empty type.

{-

  What's next?

-}

-- Fun as they are, eventually you'll get bored with
-- inductive datatypes.

-- Move on to: Families.agda