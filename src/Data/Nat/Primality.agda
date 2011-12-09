------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

module Data.Nat.Primality where

open import Data.Empty
open import Data.Fin as Fin hiding (_+_)
open import Data.Fin.Dec
open import Data.Nat
open import Data.Nat.Divisibility
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Unary

-- Definition of primality.

Prime : ℕ → Set
Prime 0             = ⊥
Prime 1             = ⊥
Prime (suc (suc n)) = (i : Fin n) → ¬ (2 + Fin.toℕ i ∣ 2 + n)

-- Decision procedure for primality.

prime? : Decidable Prime
prime? 0             = no λ()
prime? 1             = no λ()
prime? (suc (suc n)) = all? λ _ → ¬? (_ ∣? _)

private

  -- Example: 2 is prime.

  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)
