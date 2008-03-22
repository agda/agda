------------------------------------------------------------------------
-- Booleans (some core definitions)
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Bool.

module Data.Bool.Core where

------------------------------------------------------------------------
-- The type

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}
