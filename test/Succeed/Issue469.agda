{-# OPTIONS --universe-polymorphism #-}
-- There was a bug with reducing levels which could leave
-- instantiated metas in the term.
module Issue469 where

open import Common.Level

postulate
  ∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
  E : ∀ {c d} → Set c → Set d → Set (c ⊔ d)

data K : Set where
  k₁ : K

P : ∀ {e f} → K → Set e → Set f → Set (e ⊔ f)
P k₁ A B = E A B

postulate
  lemma₁ : ∀ {g h} {A : Set g} {B : Set h} → E A B → E A B

  lemma₂ :
    ∀ {i j k l} {A : Set i} {B₁ : A → Set j} {B₂ : A → Set k} →
    (∀ x → P l (B₁ x) (B₂ x)) → P l (∃ B₁) (∃ B₂)

  lemma₃ : ∀ {m n} {A₁ A₂ : Set m} → E A₁ A₂ → P n A₁ A₂

Foo : ∀ o {A : Set} {B₁ B₂ : A → Set o} →
      (∀ x → E (B₁ x) (B₂ x)) → E (∃ B₁) (∃ B₂)
Foo o B₁↔B₂ = lemma₁ (lemma₂ (λ r → lemma₃ (B₁↔B₂ r)))

-- Unsolved constraints:
--
-- o = o
--
-- This constraint shouldn't be too hard to solve...
--
-- I haven't checked, but I suspect that this code type checks using
-- Agda 2.2.10.
