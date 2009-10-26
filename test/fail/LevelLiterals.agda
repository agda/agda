-- There are no level literals in the concrete syntax. This file tests
-- if type errors use level literals.

{-# OPTIONS --universe-polymorphism #-}

module LevelLiterals where

data Level : Set where
  zero : Level
  suc  : Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}

max : Level → Level → Level
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

{-# BUILTIN LEVELMAX max #-}

data ⊥ : Set₁ where

DoubleNegated : ∀ {ℓ} → Set ℓ → Set
DoubleNegated A = (A → ⊥) → ⊥
