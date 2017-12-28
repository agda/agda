------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotients for Heterogeneous equality
------------------------------------------------------------------------

module Relation.Binary.HeterogeneousEquality.Quotients where

open import Function
open import Level hiding (lift)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning

record Quotient {c ℓ} (S : Setoid c ℓ) : Set (suc (c ⊔ ℓ)) where
  open Setoid S renaming (Carrier to A)
  field
    Q   : Set c
    abs : A → Q

  compat : (B : Q → Set c) (f : ∀ a → B (abs a)) → Set (c ⊔ ℓ)
  compat _ f = {a a′ : A} → a ≈ a′ → f a ≅ f a′

  field
    compat-abs : compat _ abs
    lift       : (B : Q → Set c) (f : ∀ a → B (abs a)) → compat B f → ∀ q → B q
    lift-conv  : {B : Q → Set c} (f : ∀ a → B (abs a)) (p : compat B f) →
                 ∀ a → lift B f p (abs a) ≅ f a

Quotients : ∀ c ℓ → Set (suc (c ⊔ ℓ))
Quotients c ℓ = (S : Setoid c ℓ) → Quotient S

module Properties {c ℓ} {S : Setoid c ℓ} (Qu : Quotient S) where

  open Setoid S renaming (Carrier to A) hiding (refl; sym; trans)
  open Quotient Qu

  module _ {B B′ : Q → Set c} {f : ∀ a → B (abs a)} {p : compat B f} where

   lift-unique : {g : ∀ q → B′ q} → (∀ a → g (abs a) ≅ f a) →
                 ∀ x → lift B f p x ≅ g x
   lift-unique {g} ext = lift _ liftf≅g liftf≅g-ext where

     liftf≅g : ∀ a → lift B f p (abs a) ≅ g (abs a)
     liftf≅g x = begin
       lift _ f p (abs x) ≅⟨ lift-conv f p x ⟩
       f x                ≅⟨ sym (ext x) ⟩
       g (abs x)          ∎

     liftf≅g-ext : ∀ {a a′} → a ≈ a′ → liftf≅g a ≅ liftf≅g a′
     liftf≅g-ext eq = ≅-heterogeneous-irrelevanceˡ _ _
                    $ cong (lift B f p) (compat-abs eq)

   lift-ext : {g : ∀ a → B′ (abs a)} {p′ : compat B′ g} → (∀ x → f x ≅ g x) →
              ∀ x → lift B f p x ≅ lift B′ g p′ x
   lift-ext {g} {p′} h = lift-unique $ λ a → begin
       lift B′ g p′ (abs a) ≅⟨ lift-conv g p′ a ⟩
       g a                  ≅⟨ sym (h a) ⟩
       f a                  ∎

  lift-conv-abs : ∀ a → lift (const Q) abs compat-abs a ≅ a
  lift-conv-abs = lift-unique (λ _ → refl)

  lift-fold : {B : Q → Set c} (f : ∀ q → B q) →
              ∀ a → lift B (f ∘ abs) (cong f ∘ compat-abs) a ≅ f a
  lift-fold f = lift-unique (λ _ → refl)

  abs-epimorphism : {B : Q → Set c} {f g : ∀ q → B q} →
                    (∀ x → f (abs x) ≅ g (abs x)) → ∀ q → f q ≅ g q
  abs-epimorphism {B} {f} {g} p q = begin
    f q                                      ≅⟨ sym (lift-fold f q) ⟩
    lift B (f ∘ abs) (cong f ∘ compat-abs) q ≅⟨ lift-ext p q ⟩
    lift B (g ∘ abs) (cong g ∘ compat-abs) q ≅⟨ lift-fold g q ⟩
    g q                                      ∎


postulate ext : ∀{a b}{A : Set a}{B B' : A → Set b}{f : ∀ a → B a}
                {g : ∀ a → B' a} → (∀ a → f a ≅ g a) → f ≅ g

module Properties₂
       {c ℓ} {S₁ S₂ : Setoid c ℓ} (Qu₁ : Quotient S₁) (Qu₂ : Quotient S₂)
       where

  module S₁  = Setoid S₁
  module S₂  = Setoid S₂
  module Qu₁ = Quotient Qu₁
  module Qu₂ = Quotient Qu₂

  module _  {B : _ → _ → Set c} (f : ∀ s₁ s₂ → B (Qu₁.abs s₁) (Qu₂.abs s₂)) where

   compat₂ : Set _
   compat₂ = ∀ {a b a′ b′} → a S₁.≈ a′ → b S₂.≈ b′ → f a b ≅ f a′ b′

   lift₂ : compat₂ → ∀ q q′ → B q q′
   lift₂ p = Qu₁.lift _ g (ext ∘ g-ext) module Lift₂ where

     g : ∀ a q → B (Qu₁.abs a) q
     g a = Qu₂.lift (B (Qu₁.abs a)) (f a) (p S₁.refl)

     g-ext : ∀ {a a′} → a S₁.≈ a′ → ∀ q → g a q ≅ g a′ q
     g-ext a≈a′ = Properties.lift-ext Qu₂ (λ _ → p a≈a′ S₂.refl)

   lift₂-conv : (p : compat₂) → ∀ a a′ → lift₂ p (Qu₁.abs a) (Qu₂.abs a′) ≅ f a a′
   lift₂-conv p a a′ = begin
     lift₂ p (Qu₁.abs a) (Qu₂.abs a′)
        ≅⟨ cong (_$ (Qu₂.abs a′)) (Qu₁.lift-conv (Lift₂.g p) (ext ∘ Lift₂.g-ext p) a) ⟩
     Lift₂.g p a (Qu₂.abs a′)
        ≡⟨⟩
     Qu₂.lift (B (Qu₁.abs a)) (f a) (p S₁.refl) (Qu₂.abs a′)
        ≅⟨ Qu₂.lift-conv (f a) (p S₁.refl) a′ ⟩
     f a a′
        ∎

module Properties₃ {c ℓ} {S₁ S₂ S₃ : Setoid c ℓ}
       (Qu₁ : Quotient S₁) (Qu₂ : Quotient S₂) (Qu₃ : Quotient S₃)
       where

  module S₁  = Setoid S₁
  module S₂  = Setoid S₂
  module S₃  = Setoid S₃
  module Qu₁ = Quotient Qu₁
  module Qu₂ = Quotient Qu₂
  module Qu₃ = Quotient Qu₃

  module _ {B : _ → _ → _ → Set c}
           (f : ∀ s₁ s₂ s₃ → B (Qu₁.abs s₁) (Qu₂.abs s₂) (Qu₃.abs s₃)) where

   compat₃ : Set _
   compat₃ = ∀ {a b c a′ b′ c′} → a S₁.≈ a′ → b S₂.≈ b′ → c S₃.≈ c′ →
             f a b c ≅ f a′ b′ c′

   lift₃ : compat₃ → ∀ q₁ q₂ q₃ → B q₁ q₂ q₃
   lift₃ p = Qu₁.lift _ h (ext ∘ h-ext) module Lift₃ where

     g : ∀ a b q → B (Qu₁.abs a) (Qu₂.abs b) q
     g a b = Qu₃.lift (B (Qu₁.abs a) (Qu₂.abs b)) (f a b) (p S₁.refl S₂.refl)

     g-ext : ∀ {a a′ b b′} → a S₁.≈ a′ → b S₂.≈ b′ → ∀ c → g a b c ≅ g a′ b′ c
     g-ext a≈a′ b≈b′ = Properties.lift-ext Qu₃ (λ _ → p a≈a′ b≈b′ S₃.refl)

     h : ∀ a q₂ q₃ → B (Qu₁.abs a) q₂ q₃
     h a = Qu₂.lift (λ b → ∀ q → B (Qu₁.abs a) b q) (g a) (ext ∘ g-ext S₁.refl)

     h-ext : ∀ {a a′} → a S₁.≈ a′ → ∀ b → h a b ≅ h a′ b
     h-ext a≈a′ = Properties.lift-ext Qu₂ $ λ _ → ext (g-ext a≈a′ S₂.refl)
