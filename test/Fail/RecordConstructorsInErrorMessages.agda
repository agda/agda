-- This file tests that record constructors are used in error
-- messages, if possible.

-- Andreas, 2016-07-20 Repaired this long disfunctional test case.

module RecordConstructorsInErrorMessages where

record R : Set₁ where
  constructor con
  field
    {A}         : Set
    f           : A → A
    {B C} D {E} : Set
    g           : B → C → E

postulate
  A : Set
  r : R

data _≡_ {A : Set₁} (x : A) : A → Set where
  refl : x ≡ x

foo : r ≡ record
  { A = A
  ; f = λ x → x
  ; B = A
  ; C = A
  ; D = A
  ; g = λ x _ → x
  }
foo = refl

-- EXPECTED ERROR:
-- .R.A r != A of type Set
-- when checking that the expression refl has type
-- r ≡ con (λ x → x) A (λ x _ → x)
