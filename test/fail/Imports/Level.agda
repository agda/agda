------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

module Imports.Level where

postulate
  Level : Set
  zero : Level
  suc  : (i : Level) → Level
  _⊔_ : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

infixl 6 _⊔_

