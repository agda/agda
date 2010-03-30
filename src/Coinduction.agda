------------------------------------------------------------------------
-- Basic types related to coinduction
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Coinduction where

import Level

------------------------------------------------------------------------
-- A type used to make recursive arguments coinductive

-- See Data.Colist for examples of how this type is used, or
-- http://article.gmane.org/gmane.comp.lang.agda/633 for a longer
-- explanation.

infix 10 ♯_

codata ∞ {a} (A : Set a) : Set a where
  ♯_ : (x : A) → ∞ A

♭ : ∀ {a} {A : Set a} → ∞ A → A
♭ (♯ x) = x

------------------------------------------------------------------------
-- Rec, a type which is analogous to the Rec type constructor used in
-- (the current version of) ΠΣ

record Rec {a} (A : ∞ (Set a)) : Set a where
  constructor fold
  field
    unfold : ♭ A

open Rec public

{-

  -- If --guardedness-preserving-type-constructors is enabled one can
  -- define types like ℕ by recursion:

  open import Data.Sum
  open import Data.Unit

  ℕ : Set
  ℕ = ⊤ ⊎ Rec (♯ ℕ)

  zero : ℕ
  zero = inj₁ _

  suc : ℕ → ℕ
  suc n = inj₂ (fold n)

  ℕ-rec : (P : ℕ → Set) →
          P zero →
          (∀ n → P n → P (suc n)) →
          ∀ n → P n
  ℕ-rec P z s (inj₁ _)        = z
  ℕ-rec P z s (inj₂ (fold n)) = s n (ℕ-rec P z s n)

  -- This feature is very experimental, though: it may lead to
  -- inconsistencies.

-}
