------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

module Common.Level where

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

{-# IMPORT Common.FFI #-}
{-# COMPILED_DATA Level Common.FFI.Level Common.FFI.Zero Common.FFI.Suc #-}

infixl 6 _⊔_

_⊔_ : Level -> Level -> Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}
