
open import Auto.Prelude


-- using a type argument as a proof

h0 : (x₁ x₂ : ⊥) → x₁ ≡ x₂
h0 = {!!}
--h0 = λ x₁ → λ ()


-- using dependent pair to define non-dep pair

module DND where
 _×_ : Set → Set → Set
 A × B = Σ A (λ _ → B)

 h1-2 : ∀ {A B} → A × B → B × A
-- h1-2 = {!!}  -- no solution found
 h1-2 = λ h → Σ-i {!!} {!!}
-- h1-2 = λ h → Σ-i (Σ.prf h) (Σ.wit h)

