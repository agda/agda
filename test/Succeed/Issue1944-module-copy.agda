-- Andreas, 2016-04-26 flight home from AIM XXIII

module _ where

module M (A : Set) where
  record R : Set where
    field f : A

module H {A} = M A

open M using (R)
open M.R using (f)  -- f : {A : Set} → R A → A
open H.R using (f)  -- f : {A : Set} → R A → A

r : ∀ A (a : A) → R A
f (r A a) = a

test : ∀ A (a : A) → A
test A a = f (r A a)

test' : ∀ A (a : A) → A
test' A a = f {A = _} (r A a)
