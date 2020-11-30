-- Andreas, Bengtfest 2016-04-28 Marsstrand
-- Issue 1944: also resolve overloaded projections in checking position

module _ (A : Set) (a : A) where

record R B : Set where
  field f : B
open R

record S B : Set where
  field f : B
open S

test : ∀{A : Set} → A → A
test = f
-- Expected error:
-- Cannot resolve overloaded projection f because first visible
-- argument is not of record type
-- when checking that the expression f has type .A → .A
