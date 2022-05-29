{-# OPTIONS --type-in-type --rewriting #-}

module _ where

postulate
  _≡_ : {A : Set} → A → A → Set

{-# BUILTIN REWRITE _≡_ #-}

record ⊤ : Set where
  constructor []
open ⊤

postulate
  ID : (Δ : Set) (δ₀ δ₁ : Δ) → Set
  ID⊤ : (δ₀ δ₁ : ⊤) → ID ⊤ δ₀ δ₁ ≡ ⊤
  Id : {Δ : Set} (A : Δ → Set) {δ₀ δ₁ : Δ} (δ₂ : ID Δ δ₀ δ₁) (a₀ : A δ₀) (a₁ : A δ₁) → Set
  ap : {Δ : Set} {A : Δ → Set} (f : (δ : Δ) → A δ) {δ₀ δ₁ : Δ} (δ₂ : ID Δ δ₀ δ₁) → Id A δ₂ (f δ₀) (f δ₁)
  AP : {Θ Δ : Set} (f : Θ → Δ) {t₀ t₁ : Θ} (t₂ : ID Θ t₀ t₁) → ID Δ (f t₀) (f t₁)
  Id-AP : {Θ Δ : Set} (f : Θ → Δ) {t₀ t₁ : Θ} (t₂ : ID Θ t₀ t₁) (A : Δ → Set) (a₀ : A (f t₀)) (a₁ : A (f t₁)) →
    Id A (AP f t₂) a₀ a₁ ≡ Id (λ w → A (f w)) t₂ a₀ a₁
  Copy : Set → Set
  uncopy : {A : Set} → Copy A → A

{-# REWRITE ID⊤ #-}
{-# REWRITE Id-AP #-}

postulate
  utr→ : {Δ : Set} (A : Δ → Set) {δ₀ δ₁ : Δ} (δ₂ : ID Δ δ₀ δ₁) (a₁ a₁' : A δ₁) → Id {⊤} (λ _ → A δ₁) [] a₁ a₁'
  IdU : {Δ : Set} {δ₀ δ₁ : Δ} (δ₂ : ID Δ δ₀ δ₁) (A B : Set) →
    Id {Δ} (λ _ → Set) δ₂ A B ≡ Copy ((b₀ : B) (b₁ : B) → Id {⊤} (λ _ → B) [] b₀ b₁)

{-# REWRITE IdU #-}

postulate
  apU : {Δ : Set} (A : Δ → Set) {δ₀ δ₁ : Δ} (δ₂ : ID Δ δ₀ δ₁) → uncopy (ap A δ₂) ≡ utr→ A δ₂

{-# REWRITE apU #-}
