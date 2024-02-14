module LossyInstanceFields3 where

open Agda.Primitive renaming (Set to Type ; Setω to Typeω)

record Membership {ℓ ℓ'} (ℙA : Type ℓ) (A : Type ℓ') ℓ'' : Typeω where
  field
    _∈_ : A → ℙA → Type ℓ''

open Membership ⦃ ... ⦄ using (_∈_)

test1 : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {ℙA : Type ℓ'} ⦃ memb : Membership ℙA A ℓ'' ⦄ → ℙA → ℙA → Type _
test1 S T = ∀ x → x ∈ S → x ∈ T
