
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality using (_≡_; refl)

record Container (s p : Level) : Set (lsuc (s ⊔ p)) where
  constructor _▷_
  field
    Shape    : Set s
    Position : Shape → Set p
open Container public

⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ⊔ p ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ S λ s → (P s → X)

data W {s} {p} (C : Container s p) : Set (s ⊔ p) where
  sup : ⟦ C ⟧ (W C) → W C

postulate
  s p : Level
  C : Container s p
  sh th : Shape C
  f : Position C sh → W C

postulate sup-injective₁ : ∀ {g} → sup (sh , f) ≡ sup (th , g)
