-- submitted by Nisse, 2011-06-21
module Issue423 where

------------------------------------------------------------------------
-- Prelude

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

-- Andreas: changed lhs variables to lambda-abstractions
-- This should be done automatically (internally).
curry : {A C : Set} {B : A → Set} →
        (Σ A B → C) → ((x : A) → B x → C)
curry f = \ x y -> f (x , y)

uncurry : {A C : Set} {B : A → Set} →
          ((x : A) → (y : B x) → C) → (Σ A B → C)
uncurry f = \ p -> f (Σ.proj₁ p) (Σ.proj₂ p)

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


-- The following equality holds definitionally.

equal : (τ : (γ : Env Γ) → El (σ γ) → U) →
        curry (uncurry τ) ≡ τ
equal τ = refl

-- Bug was:
-- However, the two sides behave differently.

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
