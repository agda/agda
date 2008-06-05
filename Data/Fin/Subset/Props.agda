------------------------------------------------------------------------
-- Some properties about subsets
------------------------------------------------------------------------

module Data.Fin.Subset.Props where

open import Data.Nat
open import Data.Empty
open import Data.Function
open import Data.Fin
open import Data.Fin.Subset
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Constructor mangling

fin-0-∅ : Fin zero -> ⊥
fin-0-∅ ()

zero∉ : forall {n} {p : Subset n} -> zero ∉ p ▻ outside
zero∉ ()

drop-sucIn : forall {s n x} {p : Subset n} -> suc x ∈ p ▻ s -> x ∈ p
drop-sucIn (sucIn x∈p) = x∈p

drop-▻-⊆ :  forall {n s₁ s₂} {p₁ p₂ : Subset n}
         -> p₁ ▻ s₁ ⊆ p₂ ▻ s₂ -> p₁ ⊆ p₂
drop-▻-⊆ p₁s₁⊆p₂s₂ x∈p₁ = drop-sucIn $ p₁s₁⊆p₂s₂ (sucIn x∈p₁)

drop-▻-Empty :  forall {n s} {p : Subset n}
             -> Empty (p ▻ s) -> Empty p
drop-▻-Empty ¬¬∅ ¬∅ = contradiction (_ , (sucIn $ proj₂ ¬∅)) ¬¬∅

------------------------------------------------------------------------
-- More interesting properties

allInside : forall {n} (x : Fin n) -> x ∈ all inside
allInside zero    = zeroIn
allInside (suc x) = sucIn (allInside x)

allOutside : forall {n} (x : Fin n) -> x ∉ all outside
allOutside zero    ()
allOutside (suc x) (sucIn x∈) = allOutside x x∈

⊆⊇⟶≡ :  forall {n} {p₁ p₂ : Subset n}
     -> p₁ ⊆ p₂ -> p₂ ⊆ p₁ -> p₁ ≡ p₂
⊆⊇⟶≡ = helper _ _
  where
  helper : forall {n} (p₁ p₂ : Subset n)
         -> p₁ ⊆ p₂ -> p₂ ⊆ p₁ -> p₁ ≡ p₂
  helper ε             ε              _   _   = ≡-refl
  helper (p₁ ▻ s₁)     (p₂ ▻ s₂)      ₁⊆₂ ₂⊆₁ with ⊆⊇⟶≡ (drop-▻-⊆ ₁⊆₂)
                                                        (drop-▻-⊆ ₂⊆₁)
  helper (p ▻ outside) (.p ▻ outside) ₁⊆₂ ₂⊆₁ | ≡-refl = ≡-refl
  helper (p ▻ inside)  (.p ▻ inside)  ₁⊆₂ ₂⊆₁ | ≡-refl = ≡-refl
  helper (p ▻ outside) (.p ▻ inside)  ₁⊆₂ ₂⊆₁ | ≡-refl with ₂⊆₁ zeroIn
  ...                                                  | ()
  helper (p ▻ inside)  (.p ▻ outside) ₁⊆₂ ₂⊆₁ | ≡-refl with ₁⊆₂ zeroIn
  ...                                                  | ()

∅⟶allOutside
  :  forall {n} {p : Subset n}
  -> Empty p -> p ≡ all outside
∅⟶allOutside {p = ε}     ¬¬∅ = ≡-refl
∅⟶allOutside {p = p ▻ s} ¬¬∅ with ∅⟶allOutside (drop-▻-Empty ¬¬∅)
∅⟶allOutside {p = .(all outside) ▻ outside} ¬¬∅ | ≡-refl = ≡-refl
∅⟶allOutside {p = .(all outside) ▻ inside}  ¬¬∅ | ≡-refl =
    contradiction (_ , zeroIn) ¬¬∅
