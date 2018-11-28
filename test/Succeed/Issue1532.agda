{-# OPTIONS --overlapping-instances #-}

module _ where

infixr 5 _⇒_
infixl 6 _▻_
infix  3 _⊢_ _∈_
infixr 5 vs_
infixr 4 ƛ_
infixl 6 _·_

data Type : Set where
  ι   : Type
  _⇒_ : Type → Type → Type

data Con : Set where
  ε   : Con
  _▻_ : Con → Type → Con

data _∈_ σ : Con → Set where
  vz  : ∀ {Γ}   → σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} → σ ∈ Γ     → σ ∈ Γ ▻ τ

data _⊢_ Γ : Type → Set where
  var : ∀ {σ}   → σ ∈ Γ     → Γ ⊢ σ
  ƛ_  : ∀ {σ τ} → Γ ▻ σ ⊢ τ → Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} → Γ ⊢ σ ⇒ τ → Γ ⊢ σ     → Γ ⊢ τ

Term : Type → Set
Term σ = ε ⊢ σ

postulate
  _extends_ : Con → Con → Set

  instance
    extends-stop : ∀ {Γ} → Γ extends Γ
    extends-skip : ∀ {Γ Δ σ} {{_ : Δ extends Γ}} → (Δ ▻ σ) extends Γ

  lam : ∀ {Γ σ τ} → ((∀ {Δ} {{_ : Δ extends (Γ ▻ σ)}} → Δ ⊢ σ) → Γ ▻ σ ⊢ τ) → Γ ⊢ σ ⇒ τ

I : Term (ι ⇒ ι)
I = lam λ x → x

K : Term (ι ⇒ ι ⇒ ι)
K = lam λ x → lam λ y → x

A : Term ((ι ⇒ ι) ⇒ ι ⇒ ι)
A = lam λ f → lam λ x → f {{extends-skip {{extends-stop}}}} · x
                            {{extends-stop}}

loop : Term ((ι ⇒ ι) ⇒ ι ⇒ ι)
loop = lam λ f → lam λ x → f · x
