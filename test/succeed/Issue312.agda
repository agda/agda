
module Issue312 where

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

_×_ : Set → Set → Set
A × B = Σ[ _ ∶ A ] B

postulate
  T : Set → Set → Set
  equal : ∀ {A} → T A A
  _and_are_ : (A B : Set) → T A B → Set

  -- Check that it parses to the right thing
  check : ∀ A B → (A × B) and Σ A (λ x → B) are equal
