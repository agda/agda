------------------------------------------------------------------------
-- Sizes for Agda's sized types
------------------------------------------------------------------------

module Size where

postulate
  Size : Set
  ↑_   : Size → Size
  ∞    : Size

{-# BUILTIN SIZE    Size #-}
{-# BUILTIN SIZESUC ↑_   #-}
{-# BUILTIN SIZEINF ∞    #-}
