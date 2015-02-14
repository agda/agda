------------------------------------------------------------------------
-- From the Agda standard library
--
-- Sizes for Agda's sized types
------------------------------------------------------------------------

module Common.Size where

{-# BUILTIN SIZEUNIV SizeUniv #-}  --  sort SizeUniv
{-# BUILTIN SIZE     Size     #-}  --  Size   : SizeUniv
{-# BUILTIN SIZELT   Size<_   #-}  --  Size<_ : Size → SizeUniv
{-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_     : Size → Size
{-# BUILTIN SIZEINF  ∞        #-}  --  ∞      : Size
