-- Andreas, 2012-01-10 
-- {-# OPTIONS -v tc.constr.findInScope:50 #-}
module InstanceGuessesMeta where

data Bool : Set where
  true false : Bool

postulate
  D : Bool -> Set
  E : Bool -> Set
  d : {x : Bool} -> D x
  f : {x : Bool}{{ dx : D x }} -> E x
  
b : E true
b = f  -- should succeed
-- Agda is now allowed to solve hidden x in type of d by unification, 
-- when searching for inhabitant of D x 