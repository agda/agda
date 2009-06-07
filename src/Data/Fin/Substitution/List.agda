------------------------------------------------------------------------
-- Application of substitutions to lists, along with various lemmas
------------------------------------------------------------------------

-- This module illustrates how Data.Fin.Substitution.Lemmas.AppLemmas
-- can be used.

open import Data.Fin.Substitution.Lemmas

module Data.Fin.Substitution.List {T} (lemmas₄ : Lemmas₄ T) where

open import Data.List
open import Data.List.Properties
open import Data.Fin.Substitution
import Data.Function as Fun
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

private
  open module L = Lemmas₄ lemmas₄ using (_/_; id; _⊙_)

infixl 8 _//_

_//_ : ∀ {m n} → List (T m) → Sub T m n → List (T n)
ts // ρ = map (λ σ → σ / ρ) ts

appLemmas : AppLemmas (λ n → List (T n)) T
appLemmas = record
  { application = record { _/_ = _//_ }
  ; lemmas₄     = lemmas₄
  ; id-vanishes = λ ts → begin
      ts // id       ≡⟨ map-cong L.id-vanishes ts ⟩
      map Fun.id ts  ≡⟨ map-id ts ⟩
      ts             ∎
  ; /-⊙ = λ {_ _ _ ρ₁ ρ₂} ts → begin
      ts // ρ₁ ⊙ ρ₂               ≡⟨ map-cong L./-⊙ ts ⟩
      map (λ σ → σ / ρ₁ / ρ₂) ts  ≡⟨ map-compose ts ⟩
      ts // ρ₁ // ρ₂              ∎
  }

open AppLemmas appLemmas public
  hiding (_/_) renaming (_/✶_ to _//✶_)
