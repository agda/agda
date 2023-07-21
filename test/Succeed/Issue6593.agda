-- Andreas, 2023-05-29, issue #6593
-- Temporary regression in 2.6.4 (unreleased) reported by @nad.
-- Fixed by reverting type-directed occurs check.

{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

_ : (f : ⊤ → ⊤) → _≡_ {A = ⊤ → ⊤} (λ _ → tt) f
_ = λ _ → refl {x = λ _ → tt}

-- Should succeed.
