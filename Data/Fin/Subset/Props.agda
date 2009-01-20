------------------------------------------------------------------------
-- Some properties about subsets
------------------------------------------------------------------------

module Data.Fin.Subset.Props where

open import Data.Nat
open import Data.Vec hiding (_∈_)
open import Data.Empty
open import Data.Function
open import Data.Fin
open import Data.Fin.Subset
open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Constructor mangling

drop-there : ∀ {s n x} {p : Subset n} → suc x ∈ s ∷ p → x ∈ p
drop-there (there x∈p) = x∈p

drop-∷-⊆ : ∀ {n s₁ s₂} {p₁ p₂ : Subset n} → s₁ ∷ p₁ ⊆ s₂ ∷ p₂ → p₁ ⊆ p₂
drop-∷-⊆ p₁s₁⊆p₂s₂ x∈p₁ = drop-there $ p₁s₁⊆p₂s₂ (there x∈p₁)

drop-∷-Empty : ∀ {n s} {p : Subset n} → Empty (s ∷ p) → Empty p
drop-∷-Empty ¬¬∅ (x , x∈p) = ¬¬∅ (suc x , there x∈p)

------------------------------------------------------------------------
-- More interesting properties

allInside : ∀ {n} (x : Fin n) → x ∈ all inside
allInside zero    = here
allInside (suc x) = there (allInside x)

allOutside : ∀ {n} (x : Fin n) → x ∉ all outside
allOutside zero    ()
allOutside (suc x) (there x∈) = allOutside x x∈

⊆⊇⟶≡ : ∀ {n} {p₁ p₂ : Subset n} →
       p₁ ⊆ p₂ → p₂ ⊆ p₁ → p₁ ≡ p₂
⊆⊇⟶≡ = helper _ _
  where
  helper : ∀ {n} (p₁ p₂ : Subset n) →
           p₁ ⊆ p₂ → p₂ ⊆ p₁ → p₁ ≡ p₂
  helper []            []             _   _   = refl
  helper (s₁ ∷ p₁)     (s₂ ∷ p₂)      ₁⊆₂ ₂⊆₁ with ⊆⊇⟶≡ (drop-∷-⊆ ₁⊆₂)
                                                        (drop-∷-⊆ ₂⊆₁)
  helper (outside ∷ p) (outside ∷ .p) ₁⊆₂ ₂⊆₁ | refl = refl
  helper (inside  ∷ p) (inside  ∷ .p) ₁⊆₂ ₂⊆₁ | refl = refl
  helper (outside ∷ p) (inside  ∷ .p) ₁⊆₂ ₂⊆₁ | refl with ₂⊆₁ here
  ...                                                | ()
  helper (inside  ∷ p) (outside ∷ .p) ₁⊆₂ ₂⊆₁ | refl with ₁⊆₂ here
  ...                                                | ()

∅⟶allOutside : ∀ {n} {p : Subset n} →
               Empty p → p ≡ all outside
∅⟶allOutside {p = []}     ¬¬∅ = refl
∅⟶allOutside {p = s ∷ ps} ¬¬∅ with ∅⟶allOutside (drop-∷-Empty ¬¬∅)
∅⟶allOutside {p = outside ∷ .(all outside)} ¬¬∅ | refl = refl
∅⟶allOutside {p = inside  ∷ .(all outside)} ¬¬∅ | refl =
  ⊥-elim (¬¬∅ (zero , here))
