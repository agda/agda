
-- This module gives an introduction to the module system of Agda.

module Introduction.Modules where

---------------------------------------------------------------------------
-- Simple sub-modules
---------------------------------------------------------------------------

-- As mentioned in 'Introduction.Basics' each file contains a single top-level
-- module. This module can contain any number of sub-modules. A sub-module is
-- declared in the same way as the top-level module, except that its name is
-- not qualified.

module Numbers where

  -- The contents of the top-level module do not have to be indented, but the
  -- contents of a sub-module do.

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

-- Outside a module its contents can be accessed using the name of the module.

one : Numbers.Nat
one = Numbers.suc Numbers.zero

-- Of course, this would get very tedious after a while, so to bring the
-- contents of a module into scope you can use an 'open' declaration.

open Numbers

two : Nat
two = suc one

-- When opening a module it is possible to control what names are brought into
-- scope. The open declaration supports three modifiers : 

--  using (x1; ..; xn)    only bring x1 .. xn into scope
--  renaming (x to y;..)  bring y into scope and make it refer to the name x
--                        from the opened module.
--  hiding (x1; ..; xn)   bring everything except x1 .. xn into scope

-- The using and hiding modifiers can be combined with renaming but not with
-- each other.

-- For example, this will bring the names z and s (and nothing else) into
-- scope as new names for zero and suc.
open Numbers using () renaming (zero to z; suc to s)

-- We can now pattern match on the renamed constructors.
plus : Nat -> Nat -> Nat
plus  z    m = m
plus (s n) m = s (plus n m)

---------------------------------------------------------------------------
-- 'private' and 'abstract'
---------------------------------------------------------------------------

-- Above we saw how to control which names are brought into scope when opening
-- a module. It is also possible to restrict what is visible outside a module
-- by declaring things 'private'. Declaring something private will only prevent
-- someone from using it outside the module, it doesn't prevent it from showing
-- up after reduction, or from it to reduce.
-- To prevent something from reducing (effectively hiding the definition) it
-- can be declared 'abstract'.

module Datastructures where

  private

    data List (A : Set) : Set where
      nil  : List A
      _::_ : A -> List A -> List A

    _++_ : {A : Set} -> List A -> List A -> List A
    nil       ++ ys = ys
    (x :: xs) ++ ys = x :: (xs ++ ys)

    reverse : {A : Set} -> List A -> List A
    reverse  nil      = nil
    reverse (x :: xs) = reverse xs ++ (x :: nil)

  -- Not making the stack operations abstract will reveal the underlying
  -- implementation, even though it's private.
  Stack : Set -> Set
  Stack A = List A

  emptyS : {A : Set} -> Stack A
  emptyS = nil

  push : {A : Set} -> A -> Stack A -> Stack A
  push x xs = x :: xs

  abstract

    -- An abstract datatype doesn't reveal its constructors
    data Queue (A : Set) : Set where
      queue : (front back : List A) -> Queue A  -- invariant : if the front is
                                                -- empty, so is the back

    -- Abstraction is contagious, anything that pattern matches on a queue must
    -- also be abstract.
    private

      -- make sure the invariant is preserved
      flip : {A : Set} -> Queue A -> Queue A
      flip (queue nil back) = queue (reverse back) nil
      flip q                = q

    -- these functions will not reduce outside the module
    emptyQ : {A : Set} -> Queue A
    emptyQ = queue nil nil

    enqueue : {A : Set} -> A -> Queue A -> Queue A
    enqueue x (queue front back) = flip (queue front (x :: back))

open Datastructures

testS = push    zero emptyS
testQ = enqueue zero emptyQ

