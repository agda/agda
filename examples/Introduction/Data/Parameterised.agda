
-- This module introduces parameterised datatypes.

module Introduction.Data.Parameterised where

-- First some of our old friends.

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Bool : Set where
  false : Bool
  true  : Bool

-- A datatype can be parameterised over a telescope, (A : Set) in the case of
-- lists. The parameters are bound in the types of the constructors.

data List (A : Set) : Set where
  nil  : List A
  cons : A -> List A -> List A

-- When using the constructors the parameters to the datatype becomes implicit
-- arguments. In this case, the types of the constructors are : 

--  nil  : {A : Set} -> List A
--  cons : {A : Set} -> A -> List A -> List A

-- So, we can write

nilNat = nil {Nat}  -- the type of this will be List Nat

-- When pattern matching on elements of a parameterised datatype you cannot
-- refer to the parameters--it wouldn't make sense to pattern match on the
-- element type of the list. So you can say

null : {A : Set} -> List A -> Bool
null  nil       = true
null (cons _ _) = false

-- but not

-- null (nil  {A})     = true
-- null (cons {A} _ _) = false

