{-# OPTIONS --cubical=no-glue #-}

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Equiv

-- should error
primitive
  primGlue : ∀ {ℓ ℓ'} (A : Set ℓ) {φ : I}
             → (T : Partial φ (Set ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
             → Set ℓ'
