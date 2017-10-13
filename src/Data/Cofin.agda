------------------------------------------------------------------------
-- The Agda standard library
--
-- "Finite" sets indexed on coinductive "natural" numbers
------------------------------------------------------------------------

module Data.Cofin where

open import Coinduction
open import Data.Conat as Conat using (Coℕ; suc; ∞ℕ)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Function

------------------------------------------------------------------------
-- The type

-- Note that Cofin ∞ℕ is /not/ finite. Note also that this is not a
-- coinductive type, but it is indexed on a coinductive type.

data Cofin : Coℕ → Set where
  zero : ∀ {n} → Cofin (suc n)
  suc  : ∀ {n} (i : Cofin (♭ n)) → Cofin (suc n)

suc-injective : ∀ {m} {p q : Cofin (♭ m)} → (Cofin (suc m) ∋ suc p) ≡ suc q → p ≡ q
suc-injective refl = refl

------------------------------------------------------------------------
-- Some operations

fromℕ : ℕ → Cofin ∞ℕ
fromℕ zero    = zero
fromℕ (suc n) = suc (fromℕ n)

toℕ : ∀ {n} → Cofin n → ℕ
toℕ zero    = zero
toℕ (suc i) = suc (toℕ i)

fromFin : ∀ {n} → Fin n → Cofin (Conat.fromℕ n)
fromFin zero    = zero
fromFin (suc i) = suc (fromFin i)

toFin : ∀ n → Cofin (Conat.fromℕ n) → Fin n
toFin zero    ()
toFin (suc n) zero    = zero
toFin (suc n) (suc i) = suc (toFin n i)
