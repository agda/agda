{-# OPTIONS --lossy-instance-fields #-}
module LossyInstanceFields where

open import Agda.Builtin.List
open import Agda.Builtin.Nat

open Agda.Primitive renaming (Set to Type ; Setω to Typeω)

record Membership {ℓ} (ℙA : Type ℓ) : Typeω where
  field
    {ℓ-elem ℓ-fibre} : Level
    element : Type ℓ-elem
    _∈_ : element → ℙA → Type ℓ-fibre

open Membership ⦃ ... ⦄ using (_∈_)

data _∈ₗ_ {ℓ} {A : Type ℓ} : A → List A → Type ℓ where
  here  : ∀ {x xs}   → x ∈ₗ (x ∷ xs)
  there : ∀ {x y xs} → x ∈ₗ xs → x ∈ₗ (y ∷ xs)

instance
  Membership-predicate : ∀ {ℓ ℓ'} {A : Type ℓ} → Membership (A → Type ℓ')
  Membership-predicate {A = A} = record { element = A ; _∈_ = λ x f → f x }

  Membership-list : ∀ {ℓ} {A : Type ℓ} → Membership (List A)
  Membership-list {A = A} = record { element = A ; _∈_ = _∈ₗ_ }

-- local instance arguments are still chosen:
test1 : ∀ {ℓ} {A : Type ℓ} ⦃ memb : Membership A ⦄ → A → A → Type _
test1 S T = ∀ x → x ∈ S → x ∈ T

-- global instance candidates are also chosen:
test2 : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → (A → Type ℓ') → Type _
test2 S T = ∀ x → x ∈ S → x ∈ T
