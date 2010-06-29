{-# OPTIONS --universe-polymorphism #-}

module Issue256 where

data Level : Set where
  zero : Level
  suc  : (i : Level) → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

level : ∀ {ℓ} → Set ℓ → Level
level {ℓ} _ = ℓ

-- termination check should fail for the following definition
ℓ : Level
ℓ = const zero (Set ℓ)

-- A : Set (suc {!ℓ!})
-- A = Set (level A)
