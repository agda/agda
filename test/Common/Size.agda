------------------------------------------------------------------------
-- From the Agda standard library
--
-- Sizes for Agda's sized types
------------------------------------------------------------------------

module Common.Size where

postulate
  Size : Set
  ↑_   : Size → Size
  ∞    : Size

{-# BUILTIN SIZE    Size #-}
{-# BUILTIN SIZESUC ↑_   #-}
{-# BUILTIN SIZEINF ∞    #-}
