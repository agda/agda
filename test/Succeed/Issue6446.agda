-- Test case reported by EDT4.
open import Agda.Primitive

Seti : (ℓ : Level) → Set(lsuc ℓ)
Seti ℓ = Set ℓ

lvl : ∀{ℓ} → Seti ℓ → Level
lvl{ℓ} _ = ℓ

type : {T : Set} → T → Seti(lvl T)
type{T} _ = T

R : {T : Set} → (P : T → Set) → (∀ x → P x) → Set
R P p = ∀ x → type(p x)
