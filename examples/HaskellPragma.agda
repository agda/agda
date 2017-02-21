module _ where

-- This example illustrates a problem we're not handling with the Haskell
-- language pragma.

data Bool : Set where
  t f : Bool

postulate
  axiom : Bool

fun : Bool
fun = axiom
