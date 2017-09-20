
infixr 2 _×_
infixr 2 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

data W (A : Set) (B : A → Set) : Set where
  sup : (x : A) → ((p : B x) → W A B) → W A B

-- Should be able to get φ (λ x → (k x) , rec φ (k x)))
-- just using refine.
rec : ∀ {S P}{X : Set} → (Σ[ s ∶ S ] (P s → W S P × X) → X) → W S P → X
rec φ (sup s k) = {!!}

postulate
  A : Set
  a : A

-- Refine hole as far as possible.
-- Should get: (? , ?) , (λ x → ?) , λ x → ?
test-refine : (A × A) × (A → A) × (A → A)
test-refine = {!!}
