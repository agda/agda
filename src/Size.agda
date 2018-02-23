------------------------------------------------------------------------
-- The Agda standard library
--
-- Sizes for Agda's sized types
------------------------------------------------------------------------

module Size where

open import Agda.Builtin.Size public
  renaming ( SizeU to SizeUniv ) --  sort SizeUniv
  using    ( Size                --  Size   : SizeUniv
           ; Size<_              --  Size<_ : Size → SizeUniv
           ; ↑_ )                --  ↑_     : Size → Size
  renaming ( ω to ∞ )           --  ∞      : Size
