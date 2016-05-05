Id : {A B : Set} → (A → B) → A → B
Id F = F

syntax Id (λ X → B) = ƛ X ⟶ B

postulate
  A : Set
  a : A

example₁ : A → A
example₁ = ƛ x ⟶ x

example₂ : A → A
example₂ = ƛ !_ ⟶ !_

example₃ : A → A
example₃ = ƛ !_ ⟶ (!_)

example₄ : (A → A) → A
example₄ = ƛ !_ ⟶ ! a

example₅ : (A → A) → A
example₅ = ƛ !_ ⟶ (! a)
