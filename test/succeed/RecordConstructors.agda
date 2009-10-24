module RecordConstructors (Parameter : Set) where

-- Note that the fixity declaration has to be given outside of the
-- record definition.

infix 6 _⟨_⟩_

record R (X : Set) (Y : Set) : Set₁ where
  constructor _⟨_⟩_
  field
    {A}       : Set
    f         : A → X
    {B} D {E} : Set
    g         : B → Y → E

postulate A : Set

r : R A A
r = f ⟨ A ⟩ λ (_ : A) → f
  where
  f : A → A
  f x = x

data _≡_ {A : Set₁} (x : A) : A → Set where
  refl : x ≡ x

lemma : r ≡ record {}
lemma = refl

-- Record constructors can be overloaded.

record R′ : Set₁ where
  constructor _⟨_⟩_
  field
    T₁ T₂ T₃ : Set

data D : Set where
  _⟨_⟩_ : D

r′ : R′
r′ = A ⟨ A ⟩ A

d : D
d = _⟨_⟩_
