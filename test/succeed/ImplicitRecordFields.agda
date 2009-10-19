module ImplicitRecordFields where

record R (X Y : Set) : Set₁ where
  field
    {A}         : Set
    f           : A → A
    {B C} D {E} : Set
    g           : B → C → E → X → Y

postulate A : Set

r : R A A
r = record
  { f = f
  ; B = A
  ; D = A
  ; g = λ (_ _ _ : _) → f
  }
  where
  f : A → A
  f x = x

data _≡_ {A : Set₁} (x : A) : A → Set where
  refl : x ≡ x

lemma₁ : r ≡ record {}
lemma₁ = refl

lemma₂ : R.B r ≡ A
lemma₂ = refl
