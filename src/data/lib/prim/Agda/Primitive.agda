-- The Agda primitives (preloaded).

{-# OPTIONS --cubical-compatible --no-import-sorts --level-universe #-}

module Agda.Primitive where

------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

infixl 6 _⊔_

{-# BUILTIN PROP           Prop      #-}
{-# BUILTIN TYPE           Set       #-}
{-# BUILTIN STRICTSET      SSet      #-}

{-# BUILTIN PROPOMEGA      Propω     #-}
{-# BUILTIN SETOMEGA       Setω      #-}
{-# BUILTIN STRICTSETOMEGA SSetω     #-}

{-# BUILTIN LEVELUNIV      LevelUniv #-}

-- Level is the first thing we need to define.
-- The other postulates can only be checked if built-in Level is known.

postulate
  Level : LevelUniv

-- MAlonzo compiles Level to (). This should be safe, because it is
-- not possible to pattern match on levels.

{-# BUILTIN LEVEL Level #-}

postulate
  lzero : Level
  lsuc  : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level

{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}
