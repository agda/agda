{-# OPTIONS --universe-polymorphism #-}

module Issue204.Dependency where

postulate
  Level : Set
  zero : Level
  suc  : Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

record R (ℓ : Level) : Set (suc ℓ) where

data D (ℓ : Level) : Set (suc ℓ) where

module M {ℓ : Level} (d : D ℓ) where
