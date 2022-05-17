
{-# OPTIONS --cubical-compatible #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} (i : Fin n) → Fin (suc n)

-- From Data.Fin.Properties in the standard library (2016-12-30).
suc-injective : ∀ {o} {m n : Fin o} → Fin.suc m ≡ suc n → m ≡ n
suc-injective refl = refl
