Id₁ Id₂ Id₃ : {A B : Set} → (A → B) → A → B
Id₁ F = F
Id₂ = Id₁
Id₃ = Id₁

syntax Id₁ (λ X → B) = ƛ X ⟶ B
syntax Id₂ (λ X → B) = X ↦ B
syntax Id₃ (λ X → B) = X ↦ B •

postulate
  A : Set
  a : A

module One where

  example₀ : (A → A) → A
  example₀ = ƛ _ ⟶ a

  example₁ : A → A
  example₁ = ƛ !_! ⟶ (!_!)

  example₂ : A → A
  example₂ = ƛ !_!_ ⟶ (!_!_)

  example₃ : A → A
  example₃ = ƛ _!_! ⟶ (_!_!)

  example₄ : A → A
  example₄ = ƛ _!_!_!_ ⟶ (_!_!_!_)

  example₅ : (A → A) → (A → A)
  example₅ = ƛ !_! ⟶ λ a → ! a !

  example₆ : (A → A → A) → (A → A → A)
  example₆ = ƛ !_!_ ⟶ λ a b → ! a ! b

  example₇ : (A → A → A) → (A → A → A)
  example₇ = ƛ _!_! ⟶ λ a b → a ! b !

  example₈ : (A → A → A → A → A) → (A → A → A → A → A)
  example₈ = ƛ _!_!_!_ ⟶ λ a b c → a !_! b ! c

  example₉ : (A → A) → A
  example₉ = ƛ !_! ⟶ (! a !)

  example₁₀ : (A → A → A) → A
  example₁₀ = ƛ !_!_ ⟶ (! a ! a)

  example₁₁ : (A → A → A) → A
  example₁₁ = ƛ _!_! ⟶ (a ! a !)

  example₁₂ : (A → A → A → A → A) → (A → A)
  example₁₂ = ƛ _!_!_!_ ⟶ (a ! a !_! a)

module Two where

  example₀ : (A → A) → A
  example₀ = _ ↦ a

  example₁ : A → A
  example₁ = !_! ↦ (!_!)

  example₂ : A → A
  example₂ = !_!_ ↦ (!_!_)

  example₃ : A → A
  example₃ = _!_! ↦ (_!_!)

  example₄ : A → A
  example₄ = _!_!_!_ ↦ (_!_!_!_)

  example₅ : (A → A) → (A → A)
  example₅ = !_! ↦ λ a → ! a !

  example₆ : (A → A → A) → (A → A → A)
  example₆ = !_!_ ↦ λ a b → ! a ! b

  example₇ : (A → A → A) → (A → A → A)
  example₇ = _!_! ↦ λ a b → a ! b !

  example₈ : (A → A → A → A → A) → (A → A → A → A → A)
  example₈ = _!_!_!_ ↦ λ a b c → a !_! b ! c

  example₉ : (A → A) → A
  example₉ = !_! ↦ (! a !)

  example₁₀ : (A → A → A) → A
  example₁₀ = !_!_ ↦ (! a ! a)

  example₁₁ : (A → A → A) → A
  example₁₁ = _!_! ↦ (a ! a !)

  example₁₂ : (A → A → A → A → A) → (A → A)
  example₁₂ = _!_!_!_ ↦ (a ! a !_! a)

module Three where

  example₀ : (A → A) → A
  example₀ = _ ↦ a •

  example₁ : A → A
  example₁ = !_! ↦ (!_!) •

  example₂ : A → A
  example₂ = !_!_ ↦ (!_!_) •

  example₃ : A → A
  example₃ = _!_! ↦ (_!_!) •

  example₄ : A → A
  example₄ = _!_!_!_ ↦ (_!_!_!_) •

  example₅ : (A → A) → (A → A)
  example₅ = !_! ↦ (λ a → ! a !) •

  example₆ : (A → A → A) → (A → A → A)
  example₆ = !_!_ ↦ (λ a b → ! a ! b) •

  example₇ : (A → A → A) → (A → A → A)
  example₇ = _!_! ↦ (λ a b → a ! b !) •

  example₈ : (A → A → A → A → A) → (A → A → A → A → A)
  example₈ = _!_!_!_ ↦ (λ a b c → a !_! b ! c) •

  example₉ : (A → A) → A
  example₉ = !_! ↦ (! a !) •

  example₁₀ : (A → A → A) → A
  example₁₀ = !_!_ ↦ (! a ! a) •

  example₁₁ : (A → A → A) → A
  example₁₁ = _!_! ↦ (a ! a !) •

  example₁₂ : (A → A → A → A → A) → (A → A)
  example₁₂ = _!_!_!_ ↦ (a ! a !_! a) •
