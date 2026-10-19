module InstanceSolvesVisible2 where

record Funlike {ℓ} (A : Set) (arg : Set) (out : arg → Set ℓ) : Set ℓ where
  field
    _·_ : A → (x : arg) → out x
  infixl 999 _·_

open Funlike ⦃ ... ⦄ using (_·_) public

postulate
  Fn : Set
  fn : Fn
  A : Set
  instance i : Funlike Fn A (λ _ → Set)

_ : Set
_ = ∀ x → fn · x
