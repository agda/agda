-- Andreas, 2013-03-15 issue reported by Nisse

-- {-# OPTIONS -v tc.proj:40 -v tc.conv.elim:40 #-}
-- {-# OPTIONS -v tc.inj.check:45 #-}
-- {-# OPTIONS -v tc.proj.like:45 #-}

module Issue821 where

import Common.Level

data D (A : Set) : Set where
  c : D A → D A

-- f is projection like, but could also be injective!?
f : (A : Set) → D A → D A
f A (c x) = x

postulate
  A : Set
  P : D A → Set
  x : D A
  p : P x
  Q : P (f A x) → Set

Foo : Set₁
Foo = Q p

-- WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:466

-- Reason was that f is projection-like so the test x =?= f A x
-- actually becomes x =?= x .f with unequal spine shapes (empty vs. non-empty).
-- Agda thought this was impossible.

-- Expected error:
-- x != (f A x) of type (D A)
-- when checking that the expression p has type P (f A x)

-- Projection-likeness of f will turn this into:
-- x != (f _ x) of type (D A)
