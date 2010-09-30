------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Level where

-- Levels.

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

{-# IMPORT Level.FFI #-}
{-# COMPILED_DATA Level Level.FFI.Level Level.FFI.Zero Level.FFI.Suc #-}

-- Maximum.

infixl 6 _⊔_

_⊔_ : Level → Level → Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)

{-# BUILTIN LEVELMAX _⊔_ #-}

-- Lifting.

record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public
