{-

          Types Summer School 2007

                 Bertinoro
             Aug 19 - 31, 2007


                   Agda

                Ulf Norell

-}

-- This is where the fun begins.
-- Unleashing datatypes, pattern matching and recursion.

module Datatypes where

{-

  Simple datatypes.

-}

-- Let's define natural numbers.

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- A simple function.
pred : Nat -> Nat
pred zero    = zero
pred (suc n) = n

-- Now let's do recursion.
_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

infixl 60 _+_

-- An aside on infix operators:
-- Any name containing _ can be used as a mixfix operator.
-- The arguments simply go in place of the _. For instance:

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
-- if false then x else y = y
if_then_else_ false x y = y

{-

  Parameterised datatypes

-}

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

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

-- The Curry-Howard isomorphism.
--   CurryHoward.agda
