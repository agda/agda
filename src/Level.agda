------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Level where

-- Levels.

postulate
  Level : Set
  lzero : Level
  lsuc  : (i : Level) → Level
  _⊔_ : Level → Level → Level

{-# IMPORT Level.FFI #-}
{-# COMPILED_TYPE Level Level.FFI.Level #-}
{-# COMPILED lzero Level.FFI.Zero #-}
{-# COMPILED lsuc Level.FFI.Suc #-}

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}
{-# BUILTIN LEVELMAX _⊔_ #-}

-- Maximum.

infixl 6 _⊔_

-- Lifting.

record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public
