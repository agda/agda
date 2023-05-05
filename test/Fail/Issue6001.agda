-- Andreas, 2022-09-30, issue #6001
-- Testcase by @tomdjong, Jakob Bruenker, Amelia

-- Cubical extra-clauses cannot be generated unless
-- target is known to be fibrant.

{-# OPTIONS --cubical-compatible #-}

data Foo {A : Set} : A → Set where
  con : (x : A) → Foo x

bug : ∀ {A : Set} {a : A} {p : Foo a} → ?
bug {p = con _} = {!!}

-- WAS: internal error
-- Now:
-- Cubical Agda: cannot generate hcomp clauses at type
-- ?0
-- when checking the definition of bug
