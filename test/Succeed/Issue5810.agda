open import Agda.Primitive
open import Agda.Builtin.Unit

bad : Setω
bad = (λ (ℓ : ⊤ → Level) → ∀ t → Set (ℓ t)) (λ _ → lzero)
