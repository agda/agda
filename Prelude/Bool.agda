------------------------------------------------------------------------
-- Booleans
------------------------------------------------------------------------

module Prelude.Bool where

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

if_then_else_ : {a : Set} -> Bool -> a -> a -> a
if true  then t else f = t
if false then t else f = f
