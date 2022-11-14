{-# OPTIONS --no-load-primitives #-}
module NoLoadPrims.Base where

-- Binding the very magical built-ins works:
{-# BUILTIN TYPE Type #-}
{-# BUILTIN PROP Prop #-}
{-# BUILTIN SETOMEGA Typeω #-}
{-# BUILTIN STRICTSET SSet #-}
{-# BUILTIN STRICTSETOMEGA SSetω #-}
postulate
  Level : Type
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : Level → Level → Level
{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC lsuc #-}
{-# BUILTIN LEVELMAX _⊔_ #-}

-- Type checking works:
_ : Typeω
_ = ∀ l → Type l
