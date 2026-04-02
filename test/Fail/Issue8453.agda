-- Andreas, 2026-04-02, issue #8453
-- Report and original testcase (without --safe) by @nad
-- This testcase by @lawcho

{-# OPTIONS --cubical-compatible --safe #-}

open import Agda.Builtin.Char
open import Agda.Builtin.Maybe
open import Agda.Builtin.Unit
open import Agda.Primitive

data ⊥ : Set where

record Σ {a p} (A : Set a) (P : A → Set p) : Set (a ⊔ p) where
  field
    proj₁ : ⊥
    proj₂ : ⊥
open Σ

{-# BUILTIN SIGMA Σ #-}      -- This should fail!

{-# BUILTIN STRING Char #-}

primitive
  primStringUncons : Char → Maybe (Σ Char (λ _ → Char))

maybe-bad : Maybe ⊥
maybe-bad with primStringUncons " This is a bug!"
… | just p  = just (p .proj₂)
… | nothing = nothing

From-just : Maybe ⊥ → Set
From-just (just _) = ⊥
From-just nothing  = ⊤

from-just : (x : Maybe ⊥) → From-just x
from-just (just x) = x
from-just nothing  = tt

bad : ⊥
bad = from-just maybe-bad
