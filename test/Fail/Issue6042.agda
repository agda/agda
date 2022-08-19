{-# OPTIONS --type-in-type --rewriting --without-K #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  _＝_ : {A : Set} → A → A → Set
  refl' : {A : Set} (a : A) → (a ＝ a)
  Σ : (A : Set) (B : A → Set) → Set
  _,_ : {A : Set} {B : A → Set} (a : A) → B a → Σ A B
  fst : {A : Set} {B : A → Set} → Σ A B → A
  snd : {A : Set} {B : A → Set} (u : Σ A B) → B (fst u)
  Π : (A : Set) (B : A → Set) → Set
  𝛌 : {A : Set} {B : A → Set} (f : (x : A) → B x) → Π A B
  _∙_ : {A : Set} {B : A → Set} (f : Π A B) (a : A) → B a
  Πβ : {A : Set} {B : A → Set} (f : (x : A) → B x) (a : A) → (𝛌 f ∙ a) ≡ f a
  fstβ : {A : Set} {B : A → Set} (a : A) (b : B a) → fst {A} {B} (a , b) ≡ a

{-# REWRITE Πβ fstβ #-}

postulate
  sndβ : {A : Set} {B : A → Set} (a : A) (b : B a) → snd {A} {B} (a , b) ≡ b

{-# REWRITE sndβ #-}

Id : {A : Set} (B : Π A (λ _ → Set)) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ : B ∙ a₀) (b₁ : B ∙ a₁) → Set

postulate
  Id-const : (A B : Set) {a₀ a₁ : A} (a₂ : a₀ ＝ a₁) (b₀ b₁ : B) →
    Id {A} (𝛌 λ _ → B) a₂ b₀ b₁ ≡ (b₀ ＝ b₁)
  ＝-Π : {A : Set} {B : A → Set} (f g : Π A B) →
    (f ＝ g) ≡ Π (Σ A (λ a₀ → Σ A (λ a₁ → a₀ ＝ a₁))) (λ aₓ →
      Id (𝛌 B) (snd (snd aₓ)) (f ∙ fst aₓ) (g ∙ fst (snd aₓ)))

{-# REWRITE Id-const ＝-Π #-}

postulate
  √ : {I : Set} (A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Set) → I → Set
  dig : {I : Set} (A : (i₀ i₁ : I) (i₂ : i₀ ＝ i₁) → Set) {i₀ i₁ : I} (i₂ : i₀ ＝ i₁)
    (s₀ : √ A i₀) (s₁ : √ A i₁) (s₂ : Id (𝛌 (√ A)) i₂ s₀ s₁) → A i₀ i₁ i₂
  corr : (X : Set) → √ (λ X₀ X₁ X₂ → Π X₁ (λ _ → Set)) X

_↓ : {X₀ X₁ : Set} (X₂ : X₀ ＝ X₁) → Π X₁ (λ _ → Set)
_↓ {X₀} {X₁} X₂ = dig (λ X₀ X₁ X₂ → Π X₁ (λ _ → Set)) X₂ (corr X₀) (corr X₁) (refl' (𝛌 corr) ∙ (X₀ , (X₁ , X₂)))

Id {A} B {a₀} {a₁} a₂ b₀ b₁ = ((refl' B ∙ (a₀ , (a₁ , a₂))) ↓) ∙ b₁
