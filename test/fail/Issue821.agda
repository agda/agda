-- Andreas, 2013-03-15 issue reported by Nisse
-- {-# OPTIONS -v tc.proj:40 -v tc.conv.elim:40 #-}
module Issue821 where

import Common.Level

data D (A : Set) : Set where
  c : D A → D A

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

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:466

-- Reason was that f is projection-like so the test x =?= f A x
-- actually becomes x =?= x .f with unequal spine shapes (empty vs. non-empty).
-- Agda thought this was impossible.
