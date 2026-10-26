module CompileDefined where

open import Agda.Builtin.Nat

foo : Nat → Nat
foo x = x + x

-- Adding COMPILE to a defined function will trigger a warning,
-- since the function is already defined in Agda. The COMPILE
-- pragma may override the Agda definition at runtime, which
-- could lead to unexpected behaviour.
{-# COMPILE GHC foo = \ x -> 2 #-}
