module Issue6542.Import (M : Set) where

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma

data Term : Set where
  var : (x : Nat) → Term
  T : Term

infixl 30 _∙_
data Con : Set where
  _∙_ : Con → Term → Con

Subst : Set
Subst = Nat → Term

variable
  t A B : Term
  Γ Δ : Con
  σ : Subst

head : Subst → Term
head σ = σ zero

tail : Subst → Subst
tail σ x = σ (suc x)

liftSubst : (σ : Subst) → Subst
liftSubst σ zero    = var zero
liftSubst σ (suc x) = σ x

subst : (σ : Subst) (t : Term) → Term
subst σ (var x) = σ x
subst σ T = T

mutual
  data ⊢_ : Con → Set where
    _∙_ : ⊢ Γ → Γ ⊢ A → ⊢ Γ ∙ A

  data _⊢_ (Γ : Con) : Term → Set where
    Tⱼ : ⊢ Γ → Γ ⊢ T

record R : Set where

data _⊩T_ : (Γ : Con) (A : Term) → Set where
  Tᵣ : ⊢ Γ → Γ ⊩T T

_⊩_ : (Γ : Con) → Term → Set
Γ ⊩ A = Γ ⊩T A

_⊩_/_ : (Γ : Con) (A : Term) → Γ ⊩ A → Set
Γ ⊩ A / Tᵣ x = Γ ⊩T A

_⊩_∷_/_ : (Γ : Con) (t A : Term) → Γ ⊩ A → Set
Γ ⊩ t ∷ .T / Tᵣ x = ⊤

mutual
  data ⊩ᵛ_ : Con → Set where
    _∙_ : ∀ {A} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ A / [Γ]
        → ⊩ᵛ Γ ∙ A

  record _⊩ᵛ_/_ (Γ : Con) (A : Term) ([Γ] : ⊩ᵛ Γ) : Set where
    constructor wrap
    field
      unwrap :
        ∀ (Δ : Con) σ (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
        → Σ (Δ ⊩ subst σ A) (λ [Aσ]
        → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ / [σ])
        → Δ ⊩ subst σ A / [Aσ])

  _⊩ˢ_∷_/_/_ : (Δ : Con) (σ : Subst) (Γ : Con) ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             → Set
  Δ ⊩ˢ σ ∷ .(Γ ∙ A) / (_∙_ {Γ = Γ} {A} [Γ] [A]) / ⊢Δ =
    Σ (Δ ⊩ˢ tail σ ∷ Γ / [Γ] / ⊢Δ) λ [tailσ] →
      (Δ ⊩ head σ ∷ subst (tail σ) A / fst (_⊩ᵛ_/_.unwrap [A] _ _ ⊢Δ [tailσ]))

  _⊩ˢ_∷_/_/_/_ : (Δ : Con) (σ : Subst) (Γ : Con) ([Γ] : ⊩ᵛ Γ)
                 (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Set
  Δ ⊩ˢ σ ∷ .(Γ ∙ A) / (_∙_ {Γ = Γ} {A} [Γ] [A]) / ⊢Δ / [σ] =
    Σ (Δ ⊩ˢ tail σ ∷ Γ / [Γ] / ⊢Δ / fst [σ]) λ _ →
      (Δ ⊩ head σ ∷ subst (tail σ) A / fst (_⊩ᵛ_/_.unwrap [A] _ _ ⊢Δ (fst [σ])))

open _⊩ᵛ_/_ public

Tᵛ : ∀ ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ T / [Γ]
Tᵛ [Γ] = wrap (λ Δ σ ⊢Δ [σ] → (Tᵣ ⊢Δ) , (λ [σ≡σ′] → Tᵣ ⊢Δ))
