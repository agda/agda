------------------------------------------------------------------------
-- Booleans (some core definitions)
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Bool.

module Data.Bool.Core where

open import Data.Unit.Core
open import Data.Empty

------------------------------------------------------------------------
-- The type

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

------------------------------------------------------------------------
-- Some operations

not : Bool -> Bool
not true  = false
not false = true

-- A function mapping true to an inhabited type and false to an empty
-- type.

T : Bool -> Set
T true  = ⊤
T false = ⊥
