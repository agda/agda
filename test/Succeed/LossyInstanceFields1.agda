{-# OPTIONS --lossy-instance-fields #-}
module LossyInstanceFields1 where

open import Agda.Builtin.List
open import Agda.Builtin.Nat

open Agda.Primitive renaming (Set to Type ; Setω to Typeω)

-- Alternative definition of membership where the blocking meta might
-- appear in the instance type
--
-- Does not affect the current implementation but might allow a finer,
-- per-class choice in the future (functional dependencies??)

record Membership {ℓ ℓ'} (ℙA : Type ℓ) (A : Type ℓ') ℓ'' : Typeω where
  field
    _∈_ : A → ℙA → Type ℓ''

open Membership ⦃ ... ⦄ using (_∈_)

test1 : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {ℙA : Type ℓ'} ⦃ memb : Membership ℙA A ℓ'' ⦄ → ℙA → ℙA → Type _
test1 S T = ∀ x → x ∈ S → x ∈ T
