module _ {a} {A : Set a} where

open import Agda.Builtin.Equality
open import Agda.Builtin.List

infix 4 _⊆_

postulate
  _⊆_ : (xs ys : List A) → Set a
  ⊆-trans : ∀{xs ys zs} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs

private
  variable
    xs ys zs : List A
    σ τ : ys ⊆ zs
    x y : A
    x≈y : x ≡ y

lemma : ∀ us (ρ : us ⊆ zs) (τ' : x ∷ xs ⊆ us) (σ' : ys ⊆ us)
         (τ'∘ρ≡τ : ⊆-trans τ' ρ ≡ τ)
         (σ'∘ρ≡σ : ⊆-trans σ' ρ ≡ σ)
      → us ⊆ us
lemma {τ = τ} {σ = σ} us ρ τ' σ' τ'∘ρ≡τ σ'∘ρ≡σ =
  lem {τ = τ} {σ} us ρ τ' σ' τ'∘ρ≡τ σ'∘ρ≡σ
  where
    lem : ∀ {ys zs} {τ : (x ∷ xs) ⊆ zs} {σ : ys ⊆ zs}
         us (ρ : us ⊆ zs) (τ' : x ∷ xs ⊆ us) (σ' : ys ⊆ us)
         (τ'∘ρ≡τ : ⊆-trans τ' ρ ≡ τ)
         (σ'∘ρ≡σ : ⊆-trans σ' ρ ≡ σ) →
       {!!}
    lem = {!!}
