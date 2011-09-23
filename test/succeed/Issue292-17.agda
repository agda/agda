-- 2011-09-15 by Nisse
-- {-# OPTIONS -v tc.lhs.unify:15 #-}
module Issue292-17 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

postulate
  I  : Set
  U  : I → Set
  El : ∀ {i} → U i → Set

mutual

  infixl 5 _▻_

  data Ctxt : Set where
    _▻_ : (Γ : Ctxt) (σ : Type Γ) → Ctxt

  Type : Ctxt → Set
  Type Γ = Σ I (λ i → Env Γ → U i)

  Env : Ctxt → Set
  Env (Γ ▻ σ) = Σ (Env Γ) λ γ → El (proj₂ σ γ)

postulate
  Γ : Ctxt
  σ : Type Γ

data D : Type (Γ ▻ σ) → Set where
  d : (τ : Type Γ) → D (proj₁ τ , λ γ → proj₂ τ (proj₁ γ))

record [D] : Set where
  constructor [d]
  field
    τ : Type (Γ ▻ σ)
    x : D τ

Foo : {τ₁ τ₂ : Type Γ} →
      [d] (proj₁ τ₁ , λ γ → proj₂ τ₁ (proj₁ γ)) (d τ₁) ≡
      [d] (proj₁ τ₂ , λ γ → proj₂ τ₂ (proj₁ γ)) (d τ₂) →
      Set₁
Foo refl = Set
