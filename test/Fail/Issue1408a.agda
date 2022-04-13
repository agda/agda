{-# OPTIONS --cubical-compatible #-}

-- {-# OPTIONS -v tc.lhs.unify:15 #-}

open import Common.Equality
open import Common.Prelude

data Fin : (n : Nat) → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} (i : Fin n) → Fin (suc n)

data _≅_ {A : Set} (a : A) : {B : Set} (b : B) → Set1 where
  refl : a ≅ a

OffDiag : ∀ {n m} → Fin n → Fin m → Set
OffDiag zero    zero    = ⊥
OffDiag (suc _) (suc _) = ⊥
OffDiag _       _       = ⊤

inj-Fin-≅ : ∀ {n m} {i : Fin n} {j : Fin m} → i ≅ j → OffDiag i j → ⊥
inj-Fin-≅ {i = zero}  {zero} eq ()
inj-Fin-≅ {i = zero}  {suc j} ()
inj-Fin-≅ {i = suc i} {zero} ()
inj-Fin-≅ {i = suc i} {suc j} p ()
