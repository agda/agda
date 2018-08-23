{-# OPTIONS --universe-polymorphism #-}

module PatternMatchingOnCodata where

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

_⊔_ : Level → Level → Level
zero  ⊔ j     = j
suc i ⊔ zero  = suc i
suc i ⊔ suc j = suc (i ⊔ j)

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

infix 1000 ♯_

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

my-♭ : ∀ {a} {A : Set a} → ∞ A → A
my-♭ (♯ x) = x
