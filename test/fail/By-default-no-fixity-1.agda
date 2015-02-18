infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

LeftZero : {A : Set} → A → (A → A → A) → Set
LeftZero z _∙_ = ∀ x → z ∙ x ≡ z
