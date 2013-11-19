------------------------------------------------------------------------
-- From the Agda standard library
--
-- Sizes for Agda's sized types
------------------------------------------------------------------------

module Common.Size where

postulate
  Size   : Set
  Size<_ : Size → Set
  ↑_     : Size → Size
  ∞      : Size

{-# BUILTIN SIZE    Size   #-}
{-# BUILTIN SIZELT  Size<_ #-}
{-# BUILTIN SIZESUC ↑_     #-}
{-# BUILTIN SIZEINF ∞      #-}
