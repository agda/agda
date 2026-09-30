module Issue7196 where


postulate
  T : Set
  I : T → Set

record Foo : Set where
  field
    t : T
    instance
      I-t : I t

auto : ∀ {ℓ} {A : Set ℓ} → ⦃ A ⦄ → A
auto ⦃ a ⦄ = a

module _ (f : Foo) where -- f needs to be visible
  open Foo f
  bug : I t
  bug = {! auto !}
