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
upd-p-s : Nat → Nat → R → R
upd-p-s zero s r = record r { p = param zero; s = s }
upd-p-s (suc n) s r = record (upd-p-s n 0 r) { p = param n; s = s }

eq₁ : new ≡ new′
eq₁ = refl

eq₂ : upd-p-s zero 1 (record new { s = 0 }) ≡ old
eq₂ = refl

-- Check that instance arguments are handled properly
postulate
  T : Nat → Set
  instance
    t0 : T 0
    t1 : T 1

record Instance : Set where
  field
    n : Nat
    {{t}} : T n

r0 : Instance
r0 = record { n = 0 }

r1 : Instance
r1 = record r0 { n = 1 }

check : Instance.t r1 ≡ t1
check = refl

-- Andreas, 2020-03-27, issue #3684
-- warn only if there are invalid or duplicate fields

_ = record old { invalidField = 1 }
_ = record old { s = 1; s = 0 }
_ = record old { foo = 1; bar = 0; s = 1; s = 0 }

-- The record type R does not have the field invalidField but it would
-- have the fields i, p, s
-- when checking that the expression record old { invalidField = 1 }
-- has type R

-- Duplicate field s in record
-- when checking that the expression record old { s = 1 ; s = 0 } has
-- type R

-- /Users/abel/agda-erasure/test/Succeed/RecordUpdateSyntax.agda:59,5-50
-- The record type R does not have the fields foo, bar but it would
-- have the fields i, p
-- when checking that the expression
-- record old { foo = 1 ; bar = 0 ; s = 1 ; s = 0 } has type R

-- Duplicate field s in record
-- when checking that the expression
-- record old { foo = 1 ; bar = 0 ; s = 1 ; s = 0 } has type R
