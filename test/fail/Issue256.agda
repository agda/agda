
module Issue256 where

open import Common.Level
open import Common.Prelude

const : Bool → ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const true  x = λ _ → x
const false x = λ _ → x

level : ∀ {ℓ} → Set ℓ → Level
level {ℓ} _ = ℓ

-- termination check should fail for the following definition
ℓ : Bool → Level
ℓ b = const b lzero (Set (ℓ b))

-- A : Set (lsuc {!ℓ!})
-- A = Set (level A)
