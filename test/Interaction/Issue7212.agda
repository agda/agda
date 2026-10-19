
open import Agda.Builtin.Nat

infix 4 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : ∀ x → x ≡ x

thm₁ : 1 + 1 ≡ 2
thm₁ = {!!}

thm₂ : 1 + 1 ≡ 2
thm₂ = {!!}
