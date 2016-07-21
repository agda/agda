-- This file tests that implicit record fields are not printed out (by
-- default).

-- Andreas, 2016-07-20 Repaired this long disfunctional test case.

module ImplicitRecordFields where

record R : Set₁ where
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
-- r ≡ record { f = λ x → x ; D = A ; g = λ x _ → x }
