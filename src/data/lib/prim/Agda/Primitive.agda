-- The Agda primitives (preloaded).

module Agda.Primitive where

------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

infixl 6 _⊔_

postulate
  Level : Set
  lzero : Level
  lsuc  : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level

-- MAlonzo compiles Level to (). This should be safe, because it is
-- not possible to pattern match on levels.

{-# COMPILED_TYPE Level ()      #-}
{-# COMPILED lzero ()           #-}
{-# COMPILED lsuc  (\_ -> ())   #-}
{-# COMPILED _⊔_   (\_ _ -> ()) #-}

{-# BUILTIN LEVEL     Level  #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}
{-# BUILTIN LEVELMAX  _⊔_    #-}
