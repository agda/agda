------------------------------------------------------------------------
-- Some properties about subsets
------------------------------------------------------------------------

module Data.Fin.Subset.Props where

open import Data.Nat
open import Data.Function
open import Data.Fin
open import Data.Fin.Subset
open import Logic

------------------------------------------------------------------------
-- Constructor mangling

abstract

  fin-0-∅ : Fin zero -> ⊥
  fin-0-∅ ()

  fz∉ : forall {n} {p : Subset n} -> fz ∉ p ▻ outside
  fz∉ ()

  drop-fsIn : forall {s n x} {p : Subset n} -> fs x ∈ p ▻ s -> x ∈ p
  drop-fsIn (fsIn x∈p) = x∈p

  drop-▻-⊆ :  forall {n s₁ s₂} {p₁ p₂ : Subset n}
           -> p₁ ▻ s₁ ⊆ p₂ ▻ s₂ -> p₁ ⊆ p₂
  drop-▻-⊆ p₁s₁⊆p₂s₂ x∈p₁ = drop-fsIn $ p₁s₁⊆p₂s₂ (fsIn x∈p₁)

  drop-▻-Empty :  forall {n s} {p : Subset n}
               -> Empty (p ▻ s) -> Empty p
  drop-▻-Empty ¬¬∅ ¬∅ = contradiction (exists (fsIn $ proof ¬∅)) ¬¬∅

------------------------------------------------------------------------
-- More interesting properties

abstract

  allInside : forall {n} (x : Fin n) -> x ∈ all inside
  allInside fz     = fzIn
  allInside (fs x) = fsIn (allInside x)

  allOutside : forall {n} (x : Fin n) -> x ∉ all outside
  allOutside fz     ()
  allOutside (fs x) (fsIn x∈) = allOutside x x∈

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
    helper (p ▻ outside) (.p ▻ inside)  ₁⊆₂ ₂⊆₁ | ≡-refl with ₂⊆₁ fzIn
    ...                                                  | ()
    helper (p ▻ inside)  (.p ▻ outside) ₁⊆₂ ₂⊆₁ | ≡-refl with ₁⊆₂ fzIn
    ...                                                  | ()

  ∅⟶allOutside
    :  forall {n} {p : Subset n}
    -> Empty p -> p ≡ all outside
  ∅⟶allOutside {p = ε}     ¬¬∅ = ≡-refl
  ∅⟶allOutside {p = p ▻ s} ¬¬∅ with ∅⟶allOutside (drop-▻-Empty ¬¬∅)
  ∅⟶allOutside {p = .(all outside) ▻ outside} ¬¬∅ | ≡-refl = ≡-refl
  ∅⟶allOutside {p = .(all outside) ▻ inside}  ¬¬∅ | ≡-refl =
      contradiction (exists fzIn) ¬¬∅
