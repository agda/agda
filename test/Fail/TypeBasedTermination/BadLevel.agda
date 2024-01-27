-- Recursive level
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.BadLevel where

open import Agda.Primitive

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x
{-# NOINLINE const #-}

level : ∀ {ℓ} → Set ℓ → Level
level {ℓ} _ = ℓ

-- termination check should fail for the following definition
ℓ : Level
ℓ = const lzero (Set ℓ)
