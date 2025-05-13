{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  _≡[_]≡_ : {A B : Set} → A → A ≡ B → B → Set
  ≡[]β : {A : Set} {x y : A} → (x ≡[ refl ]≡ y) ≡ (x ≡ y)

{-# REWRITE ≡[]β #-}

postulate
  Ctx : Set
  Ty  : Ctx → Set
  Tm  : (Γ : Ctx) → Ty Γ → Set

variable
  Γ Γ₁ Γ₂ : Ctx
  A A₁ A₂ : Ty Γ
  t₁ t₂ : Tm Γ A

postulate
  Ty≡ : ∀ Γ₁ Γ₂ → Γ₁ ≡ Γ₂ → Ty Γ₁ ≡ Ty Γ₂
  Tm≡ : ∀ Γ₁ Γ₂ A₁ A₂ Γ≡ → (A≡ : A₁ ≡[ Ty≡ Γ₁ Γ₂ Γ≡ ]≡ A₂)
      → Tm Γ₁ A₁ ≡ Tm Γ₂ A₂

  foo≡  : (Γ≡ : Γ₁ ≡ Γ₂) (A≡ : A₁ ≡[ Ty≡ _ _ Γ≡ ]≡ A₂)
        → t₁ ≡[ Tm≡ _ _ _ _ Γ≡ A≡ ]≡ t₂
        → {!!}
