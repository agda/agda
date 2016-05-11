-- Andreas, 2016-05-04, discussion with Ulf
-- Projections should be treated in the same way asonstructors,
-- what parameters concerns

-- {-# OPTIONS -v tc.mod.apply:15  #-}
-- {-# OPTIONS -v tc.term.con:50 -v tc.term.def:10 #-}

module _ where

module M (A : Set) where

  data D : Set where
    c : A → D

  record R : Set where
    field f : A
    g = f
  open R public

open module N A = M A

-- After module copy, constructor parameter is still hidden

check : ∀ A → A → D A
check A x = c {A = A} x

pat : ∀ A → D A → Set
pat A (c x) = A

-- Field parameter should be hidden

infer : ∀ A → R A → A
infer A r = f r

-- and skipped on the lhs.

copat : ∀ A (a : A) → R A
f (copat A a) = a
