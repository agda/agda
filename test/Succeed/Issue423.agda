-- submitted by Nisse, 2011-06-21

-- {-# OPTIONS -v tc.lhs.unify:15 --show-implicit #-}

module Issue423 where

-- import Common.Level

------------------------------------------------------------------------
-- Prelude

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

curry : {A C : Set} {B : A → Set} →
        (Σ A B → C) → ((x : A) → B x → C)
curry f x y = f (x , y)

uncurry : {A C : Set} {B : A → Set} →
          ((x : A) → (y : B x) → C) → (Σ A B → C)
uncurry f (x , y) = f x y

------------------------------------------------------------------------
-- Preliminaries

postulate
  U  : Set
  El : U → Set

mutual

  data Ctxt : Set where
    _▻_ : (Γ : Ctxt) (σ : Type Γ) → Ctxt

  Type : Ctxt → Set
  Type Γ = Env Γ → U

  Env : Ctxt → Set
  Env (Γ ▻ σ) = Σ (Env Γ) λ γ → El (σ γ)

postulate
  Γ : Ctxt
  σ : Type Γ

------------------------------------------------------------------------
-- Problem


-- The following equalites hold definitionally.

curry∘uncurry : (τ : (γ : Env Γ) → El (σ γ) → U) →
                curry (uncurry τ) ≡ τ
curry∘uncurry τ = refl

uncurry∘curry : (τ : Env (Γ ▻ σ) → U) →
                uncurry (curry τ) ≡ τ
uncurry∘curry τ = refl

-- Bug was:
-- However, the two sides of curry∘uncurry behave differently.

works : (τ₁ τ₂ : (γ : Env Γ) → El (σ γ) → U) →
        τ₁ ≡ τ₂ → Set₁
works τ .τ refl = Set

works′ : (τ₁ τ₂ : (γ : Env Γ) → El (σ γ) → U) →
         curry (uncurry τ₁) ≡ τ₂ → Set₁
works′ τ .τ refl = Set

fails : (τ₁ τ₂ : (γ : Env Γ) → El (σ γ) → U) →
        τ₁ ≡ curry (uncurry τ₂) → Set₁
fails τ .τ refl = Set

fails′ : (τ₁ τ₂ : (γ : Env Γ) → El (σ γ) → U) →
         curry (uncurry τ₁) ≡ curry (uncurry τ₂) → Set₁
fails′ τ .τ refl = Set

-- Bug was:
-- I find it interesting that works′ works, whereas the symmetric
-- variant fails fails.

