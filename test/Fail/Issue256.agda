
module Issue256 where

open import Common.Level

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x
{-# NOINLINE const #-}

level : ∀ {ℓ} → Set ℓ → Level
level {ℓ} _ = ℓ

-- termination check should fail for the following definition
ℓ : Level
ℓ = const lzero (Set ℓ)

-- A : Set (lsuc {!ℓ!})
-- A = Set (level A)
