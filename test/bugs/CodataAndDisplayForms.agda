module CodataAndDisplayForms where

module A where

  codata C : Set where
    c : C

  foo : C → C
  foo c = c

open A public

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

lemma : foo c ≡ c
lemma = refl

-- With display forms turned on:

-- CodataAndDisplayForms.agda:17,9-13
-- foo != .CodataAndDisplayForms.c-2 of type C
-- when checking that the expression refl has type
-- foo ≡ .CodataAndDisplayForms.c-2

-- With display forms turned off:

-- CodataAndDisplayForms.agda:17,9-13
-- .CodataAndDisplayForms.A.c-0 != .CodataAndDisplayForms.c-2 of type
-- A.C
-- when checking that the expression refl has type
-- .CodataAndDisplayForms.A.c-0 ≡ .CodataAndDisplayForms.c-2
