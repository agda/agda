
open import Auto.Prelude


-- using a type argument as a proof

h0 : (x₁ x₂ : ⊥) → x₁ ≡ x₂
h0 = {!!}
--h0 = λ ()


-- using dependent pair to define non-dep pair

module DND where
 _×_ : Set → Set → Set
 A × B = Σ A (λ _ → B)

 h1-2 : ∀ {A B} → A × B → B × A
 h1-2 = {!!}
-- h1-2 = λ z → Σ-i (Σ.prf z) (Σ.wit z)
