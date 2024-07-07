-- Andreas, 2024-07-07, issue #7346
-- Reported by Mikkel Kragh Mathiesen, test case simplified by Szumi Xie.

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

data ⊥ : Set where

data N : Set where
  zero : N
  suc  : N → N
  eq   : (x : N) → suc x ≡ x

data IsSuc : N → Set where
  is-suc : (x : N) → IsSuc (suc x)
  -- x should not be forced, since N is a HIT.

all-sucs : (x : N) → IsSuc x
all-sucs x = primTransp (λ i → IsSuc (eq x i)) i0 (is-suc x)

-- This should not termination check,
-- since dot-pattern termination is off without-K.
not-suc : (x : N) → IsSuc x → ⊥
not-suc .(suc x) (is-suc x) = not-suc x (all-sucs x)
  -- This would be changed by forcing to the following,
  -- passing the termination check:
  -- not-suc (suc x) (is-suc .x) = not-suc x (all-sucs x)

nope : ⊥
nope = not-suc zero (all-sucs zero)
