module Issue6758 where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

_×_ : Set → Set → Set
X × Y = Σ X λ x → Y

is-equiv : (X Y : Set) → (X → Y) → Set
is-equiv X Y f = (Σ (Y → X) λ s → ((x : Y) → f (s x) ≡ x)) × (Σ (Y → X) λ r → ((x : X) → r (f x) ≡ x))

_≃_ : Set → Set → Set
X ≃ Y = Σ (X → Y) λ f → is-equiv X Y f

qinv : (X Y : Set) → (X → Y) → Set
qinv X Y f = Σ (Y → X) λ g → ((x : X) → g (f x) ≡ x) × ((x : Y) → f (g x) ≡ x)

postulate
  qinveq : (X : Set) (Y : Set) (f : X → Y) → qinv X Y f → X ≃ Y

γ = qinveq _ _ _ (ψ , _)
  where
    ψ : _
    ψ _ = _
    η : (x : _) → ψ ≡ x
    η _ = refl
