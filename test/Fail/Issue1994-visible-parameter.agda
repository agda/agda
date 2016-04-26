-- Andreas, 2016-04-26 flight home from AIM XXIII

module _ where

module M (A : Set) where
  record R : Set where
    field f : A

module N A = M A
module V A = M A
module H {A} = M A

open M using (R)
open N.R using (f)  -- f : (A : Set) → R A → A
open V.R using (f)  -- f : (A : Set) → R A → A

r : ∀ A (a : A) → R A
f (r A a) = a

testN : ∀ A (a : A) → A
testN A a = N.R.f A (r A a)

test : ∀ A (a : A) → A
test A a = f (r A a)
-- should fail since all of the projection candidates expect a visible parameter
-- but none is supplied here (and cannot be supplied with overloaded projections)
