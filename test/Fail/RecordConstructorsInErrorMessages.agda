-- This file tests that record constructors are used in error
-- messages, if possible.

module RecordConstructorsInErrorMessages where

record R : Set₁ where
  constructor con
  field
    {A}         : Set
    f           : A → A
    {B C} D {E} : Set
    g           : B → C → E

postulate
  A  : Set
  r₁ : R

r₂ : R
r₂ = record
  { A = A
  ; f = λ x → x
  ; B = A
  ; C = A
  ; D = A
  ; g = λ x _ → x
  }

data _≡_ {A : Set₁} (x : A) : A → Set where
  refl : x ≡ x

foo : r₁ ≡ r₂
foo = refl
