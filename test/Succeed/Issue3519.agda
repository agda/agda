
open import Agda.Primitive
open import Agda.Builtin.Sigma

variable
  ℓ₁ ℓ₂ : Level

is-universal-element : {X : Set ℓ₁} {A : X → Set ℓ₂} → Σ X A → Set (ℓ₁ ⊔ ℓ₂)
is-universal-element {ℓ₁} {ℓ₂} {X} {A} (x , a) = ∀ y → A y

fails : {X : Set ℓ₁} {A : X → Set ℓ₂} (x : X) (a : A x)
      → is-universal-element {A = _} (x , a) → (y : X) → A y -- a is yellow
fails {ℓ₁} {ℓ₂} {X = X} {A} x a u y = u y

works : ∀ {ℓ₁} {ℓ₂} {X : Set ℓ₁} {A : X → Set ℓ₂} (x : X) (a : A x)
      → is-universal-element {A = _} (x , a) → (y : X) → A y
works x a u y = u y
