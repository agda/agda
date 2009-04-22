
module Issue139 where

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
