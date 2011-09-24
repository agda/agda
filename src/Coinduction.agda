------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic types related to coinduction
------------------------------------------------------------------------

module Coinduction where

import Level

------------------------------------------------------------------------
-- A type used to make recursive arguments coinductive

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

------------------------------------------------------------------------
-- Rec, a type which is analogous to the Rec type constructor used in
-- (the current version of) ΠΣ

data Rec {a} (A : ∞ (Set a)) : Set a where
  fold : (x : ♭ A) → Rec A

unfold : ∀ {a} {A : ∞ (Set a)} → Rec A → ♭ A
unfold (fold x) = x

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
