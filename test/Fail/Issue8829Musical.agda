{-# OPTIONS --sized-types --guardedness #-}
{-# OPTIONS --no-double-check #-}

-- Andreas, 2026-11-06, issue #8829
-- Sized data types using musical coinduction are coinductive,
-- thus not lower semi-continuous in the size.
-- Successor patterns in the size do not provide termination evidence.
--
-- Split off from Issue8829Inadmissible, since the combination of
-- --sized-types and --guardedness is unsound per se.

module Issue8829Musical where

open import Agda.Builtin.Size
open import Agda.Builtin.Bool
open import Agda.Builtin.Coinduction renaming (∞ to Delay)

data Nat : Size → Set where
  zero : ∀ {i} → Nat (↑ i)
  suc  : ∀ {i} → Nat i → Nat (↑ i)

data CoNat : Size → Set where
  cozero : ∀ {i} → CoNat (↑ i)
  cosuc  : ∀ {i} → Delay (CoNat i) → CoNat (↑ i)

postulate
  cast  : {A B : Set} → A → B
  idNat : ∀ {i} → Nat i → Nat i

conat : ∀ {i} → Nat i → CoNat i → Bool
conat zero    x = true
conat (suc n) x = conat (idNat n) (cast x)
