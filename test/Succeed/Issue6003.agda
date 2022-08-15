{-# OPTIONS --type-in-type --rewriting --allow-unsolved-metas #-}

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Unit

infixl 40 _∙_
infixl 30 _∷_
infix 40 _⊘_
infixl 30 _▹_

postulate
  Id : (A : Set) → A → Set
  refl : {A : Set} (a : A) → Id A a

postulate
  A : Set

postulate
  ℿ : (A : Set) (T : A → Set) → Set
  Λ : {A : Set} {T : A → Set} → ((x : A) → T x) → ℿ A T

postulate
  _⊘_ : {A : Set} {T : A → Set} (f : ℿ A T) (a : A) → T a
  ℿβ : {A : Set} {T : A → Set} (f : (x : A) → T x) (a : A) → (Λ {A} f) ⊘ a ≡ f a
  ℿη : {T : A → Set} (f : ℿ A (λ x → T x)) → Λ (λ x → f ⊘ x) ≡ f
{-# REWRITE ℿβ ℿη #-}

_⇨_ : Set → Set → Set
A ⇨ T = ℿ A (λ _ → T)

postulate
  _▹_ : (A : Set) (B : A ⇨ Set) → Set
  _∷_ : {A : Set} {B : A ⇨ Set} (x : A) → B ⊘ x → A ▹ B
  pop : {A : Set} {B : A ⇨ Set} → A ▹ B → A
  top : {A : Set} {B : A ⇨ Set} (δ : A ▹ B) → B ⊘ (pop δ)
  popβ : {A : Set} {B : A ⇨ Set} (δ : A) (b : B ⊘ δ) → pop {A} {B} (δ ∷ b) ≡ δ
{-# REWRITE popβ #-}

postulate
  topβ : {A : Set} {B : A ⇨ Set} (δ : A) (b : B ⊘ δ) → top {A} {B} (δ ∷ b) ≡ b
{-# REWRITE topβ #-}

postulate
  ID : Set → Set
  IDε : ID ⊤ ≡ ⊤
  ID▸ⁿᵈ : (Δ : Set) (A : Set) →
    ID (Δ ▹ (Λ λ _ → A)) ≡
    ID Δ ▹ (Λ λ _ → A) ▹ (Λ λ _ → A) ▹ (Λ λ x → Id A (top (pop x)))
  _₀ : {Δ : Set} → ID Δ → Δ
{-# REWRITE IDε ID▸ⁿᵈ #-}

postulate
  ε▸₀ⁿᵈ : (A : Set) (a₀ a₁ : A) (a₂ : Id A a₀) →
    (_₀ {⊤ ▹ (Λ λ _ → A)} (tt ∷ a₀ ∷ a₁ ∷ a₂)) ≡ (tt ∷ a₀)
{-# REWRITE ε▸₀ⁿᵈ #-}

postulate
  Id⇨ : (Δ : Set) (T : Set) (f : Δ ⇨ T) →
    (Id (ℿ Δ (λ _ → T)) f) ≡ ℿ (ID Δ) (λ x → Id T (f ⊘ (x ₀)))
{-# REWRITE Id⇨ #-}

postulate
  reflΛⁿᵈ-const : (T : Set) (t : T) →
    refl {ℿ A (λ _ → T)} (Λ λ _ → t) ≡ Λ λ _ → refl t
{-# REWRITE reflΛⁿᵈ-const #-}

postulate
  ƛ : {A : Set} {B : A → Set} (f : (x : A) → B x) (x : A) → B x
  _∙_ : {A : Set} {B : A → Set} (f : (x : A) → B x) (a : A) → B a
  Πβ : {A : Set} {B : A → Set} (f : (x : A) → B x) (a : A) → (ƛ f ∙ a) ≡ f a
  Πη : {B : A → Set} (f : (x : A) → B x) → (ƛ (λ x → f ∙ x)) ≡ f
{-# REWRITE Πβ Πη #-}

postulate
  Id⇒ : (B : Set) (f : A → B) →
    (Id (A → B) f) ≡ ((a₀ a₁ : A) (a₂ : Id A a₀) → Id B (f ∙ a₀))
{-# REWRITE Id⇒ #-}

postulate
  reflƛⁿᵈ : (B : Set) (f : A → B) →
    refl f ≡ (ƛ λ a₀ → ƛ λ a₁ → ƛ λ a₂ →
      refl {ℿ (⊤ ▹ (Λ λ _ → A)) (λ _ → B)} (Λ λ x → f ∙ top x) ⊘ (tt ∷ a₀ ∷ a₁ ∷ a₂))
{-# REWRITE reflƛⁿᵈ #-}

postulate
  Σ : (A : Set) (B : A → Set) → Set
  _,_ : {A : Set} {B : A → Set} (a : A) → B a → Σ A B
  fst : {A : Set} {B : A → Set} → Σ A B → A
  snd : {B : A → Set} (u : Σ A B) → B (fst u)
  fstβ : {A : Set} {B : A → Set} (a : A) (b : B a) → fst {A} {B} (a , b) ≡ a
{-# REWRITE fstβ #-}

record IdU (A : Set) : Set where
  field
    getId : Set
open IdU

postulate
  IdUʳ : (A : Set) → Id Set A ≡ IdU A
{-# REWRITE IdUʳ #-}

Π : (A : Set) (B : A → Set) → Set
Π A B = (x : A) → B x

postulate
  Id∙ : (B : Π A (λ _ → Set)) (a : A) (b₀ : B ∙ a) →
    Id (B ∙ a) b₀ ≡ getId (refl B ∙ a ∙ a ∙ refl a)
{-# REWRITE Id∙ #-}

postulate
  IdΣ : (B : A → Set) (u : Σ A B) →
    Id (Σ A B) u ≡ Σ (Id A (fst u)) (λ p → getId (refl (ƛ B) ∙ fst u ∙ fst u ∙ p))
{-# REWRITE IdΣ #-}

postulate
  refl-fst : (B : A → Set) (u : Σ A B) → refl (fst u) ≡ fst (refl u)
{-# REWRITE refl-fst #-}

frob-refl-snd : (B : A → Set) (u : Σ A (λ x → B ∙ x)) → Id (B ∙ fst u) (snd u)
frob-refl-snd B u = {!!}
