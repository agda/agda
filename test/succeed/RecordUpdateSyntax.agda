module RecordUpdateSyntax where

open import Common.Prelude
open import Common.Equality

data Param : Nat → Set where
  param : ∀ n → Param (suc n)

record R : Set where
  field
    {i} : Nat
    p : Param i
    s : Nat

old : R
old = record { p = param 0; s = 1 }

-- Simple update, it should be able to infer the type and the implicit.
new : _
new = record old { p = param 1 }

new′ : R
new′ = record { i = 2; p = param 1; s = 1 }

-- Here's a needlessly complex update.
upd-p-s : _ → _ → _ → R
upd-p-s zero s r = record r { p = param zero; s = s }
upd-p-s (suc n) s r = record (upd-p-s n 0 r) { p = param n; s = s }

eq₁ : new ≡ new′
eq₁ = refl

eq₂ : upd-p-s zero 1 (record new { s = 0 }) ≡ old
eq₂ = refl
