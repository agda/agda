-- Andreas, 2016-05-04, issue 1954

module _ where

module P (A : Set) where
  record R : Set where
    field f : A

open module Q A = P A

module M (A : Set) (r : R A) where
  open R A r public

-- Parameter A should be hidden in R.f
works : ∀{A} → R A → A
works r = R.f r

-- Record value should not be hidden in M.f
test : ∀{A} → R A → A
test r = M.f r
