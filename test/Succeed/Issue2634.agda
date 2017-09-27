
infix 50 _∼_

postulate
  A : Set
  x : A
  _∼_ : A → A → Set

record T : Set where
  -- This fixity declaration should not be ignored.
  infix 60 _∘_
  _∘_ : A → A → A
  _∘_ _ _ = x
  field
    law : x ∘ x ∼ x

-- Some more examples

record R : Set₁ where
  infixl 6 _+_
  field
    _+_   : Set → Set → Set
    Times : Set → Set → Set
    Sigma : (A : Set) → (A → Set) → Set
    One   : Set

  infixl 7 _*_
  _*_ = _+_

  infixr 3 Σ
  syntax Σ A (λ a → B) = a ∈ A × B
  Σ = Sigma

  field
    three : One + One * One * One + One
    pair  : x ∈ One × One + One
