-- Andreas, Bentfest 2016-04-28 Marsstrand
-- Issue 1944: also resolve overloaded projections in checking position

module _ (A : Set) (a : A) where

record R (B : Set) : Set where
  field f : B
open R

record S (B : Set) : Set where
  field f : B
open S

test : R A → A
test = f

test1 : ∀{A} → R A → A
test1 = f

test2 : ∀ A → R A → A
test2 A = f {A}

postulate
  F : Set → Set
  mapF : ∀{A B} (f : A → B) → F A → F B
  fr : F (R A)

test3 : F (R A) → F A
test3 = mapF f

test4 : F (R _) → F A
test4 = mapF f

test5 : ∀{A} → F (F (R A)) → F _
test5 = mapF (mapF f)

test6 = mapF f fr
