------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic types related to coinduction
------------------------------------------------------------------------

module Coinduction where

open import Agda.Builtin.Coinduction public

------------------------------------------------------------------------
-- Rec, a type which is analogous to the Rec type constructor used in
-- ΠΣ (see Altenkirch, Danielsson, Löh and Oury. ΠΣ: Dependent Types
-- without the Sugar. FLOPS 2010, LNCS 6009.)

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
