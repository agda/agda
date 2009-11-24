{-# OPTIONS --universe-polymorphism #-}

module Issue228 where

data Level : Set where
  zero : Level
  suc  : Level → Level
  ∞    : Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

infixl 6 _⊔_

_⊔_ : Level → Level → Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)
∞     ⊔ _     = zero
_     ⊔ ∞     = zero

{-# BUILTIN LEVELMAX _⊔_ #-}

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
