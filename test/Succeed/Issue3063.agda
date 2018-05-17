
postulate
  I  : Set
  U  : I → Set
  El : ∀ {i} → U i → Set

infixr 4 _,_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

∃ : ∀ {A : Set} → (A → Set) → Set
∃ = Σ _

mutual

  infixl 5 _▻_

  data Ctxt : Set where
    _▻_ : (Γ : Ctxt) → Type Γ → Ctxt

  Type : Ctxt → Set
  Type Γ = ∃ λ i → Env Γ → U i

  Env : Ctxt → Set
  Env (Γ ▻ σ) = Σ (Env Γ) λ γ → El (proj₂ σ γ)

mutual

  data Ctxt⁺ (Γ : Ctxt) : Set where
    _▻_ : (Γ⁺ : Ctxt⁺ Γ) → Type (Γ ++ Γ⁺) → Ctxt⁺ Γ

  infixl 5 _++_

  _++_ : (Γ : Ctxt) → Ctxt⁺ Γ → Ctxt
  Γ ++ (Γ⁺ ▻ σ) = (Γ ++ Γ⁺) ▻ σ

data P : (Γ : Ctxt) → Type Γ → Set where
  c : ∀ {Γ σ τ} → P (Γ ▻ σ) τ

f : ∀ {Γ} → Ctxt⁺ Γ → Set₁
f {Γ} (Γ⁺ ▻ σ) = Set
  where
  g : ∀ τ → P (Γ ++ Γ⁺ ▻ σ) τ → Set₁
  g _ c = Set
