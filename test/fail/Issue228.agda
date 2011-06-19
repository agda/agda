{-# OPTIONS --universe-polymorphism #-}

module Issue228 where

postulate
  Level : Set
  zero : Level
  suc  : Level → Level
  ∞    : Level
  _⊔_  : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

infixl 6 _⊔_


data _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  _,_ : A → B → A × B

data Large : Set ∞ where
  large : Large

data Small : Set₁ where
  small : Set → Small

P : Set
P = Large × Small

[_] : Set → P
[ A ] = (large , small A)

potentially-bad : P
potentially-bad = [ P ]
