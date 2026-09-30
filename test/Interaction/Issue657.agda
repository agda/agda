-- Andreas, 2017-07-28, issue #657 is fixed
-- WAS: display form problem

postulate
  A : Set
  x : A

record R (A : Set) : Set₁ where
  field
    P : A → Set

module M (r : ∀ A → R A) where

  open module R′ {A} = R (r A) public

postulate
  r : ∀ A → R A

open M r

p : P x
p = {!!}

-- WAS: goal displayed as  R.P (r A) x

-- Expected: P x
