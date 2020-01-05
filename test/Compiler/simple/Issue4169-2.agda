module _ where

import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Primitive
open import Common.IO

data ⊥ : Set where

record R₁ a : Set (lsuc a) where
  field
    R : {A : Set a} → A → A → Set a
    r : {A : Set a} (x : A) → R x x

  P : Set a → Set a
  P A = (x y : A) → R x y

record R₂ (r : ∀ ℓ → R₁ ℓ) : Set₁ where
  field
    f :
      {X Y : Σ Set (R₁.P (r lzero))} →
      R₁.R (r (lsuc lzero)) X Y → fst X → fst Y

module M (r₁ : ∀ ℓ → R₁ ℓ) (r₂ : R₂ r₁) where

  open module R₁′ {ℓ} = R₁ (r₁ ℓ) public using (P)
  open module R₂′     = R₂ r₂     public

  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  p : P ⊥
  p x = ⊥-elim x

open Agda.Builtin.Equality

r₁ : ∀ ℓ → R₁ ℓ
R₁.R (r₁ _) = _≡_
R₁.r (r₁ _) = λ _ → refl

r₂ : R₂ r₁
R₂.f r₂ refl x = x

open M r₁ r₂

data Unit : Set where
  unit : Unit

g : Σ Unit λ _ → P (Σ Set P) → ⊥
g = unit , λ h → f (h (⊤ , λ _ _ → refl) (⊥ , p)) tt

main : IO ⊤
main = return _
