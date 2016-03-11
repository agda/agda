data _≡_ {a} {A : Set a} (x : A) : A → Set a where
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
  Ctxt : Set
  Env  : Ctxt → Set

Type : Ctxt → Set
Type Γ = Σ I λ i → Env Γ → U i

Value : (Γ : Ctxt) → Type Γ → Set
Value Γ σ = (γ : Env Γ) → El (proj₂ σ γ)

_/id : ∀ {Γ} → Type Γ → Type Γ
(i , σ) /id = i , σ

data [Type] : Set where
  [_] : ∀ {Γ} → Type Γ → [Type]

_≅-Type_ : ∀ {Γ} (σ₁ σ₂ : Type Γ) → Set
σ₁ ≅-Type σ₂ = [ σ₁ ] ≡ [ σ₂ ]

data [Value] : Set where
  [_] : ∀ {Γ σ} → Value Γ σ → [Value]

_≅-Value_ : ∀ {Γ σ} (v₁ v₂ : Value Γ σ) → Set
v₁ ≅-Value v₂ = [Value].[ v₁ ] ≡ [ v₂ ]

Foo : ∀ {Γ} {σ₁ σ₂ : Type Γ} {v : Value Γ (σ₁ /id)} →
      σ₁ ≅-Type σ₂ → v ≅-Value v → Set₁
Foo refl refl = Set
