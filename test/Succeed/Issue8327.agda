-- Andreas, 2026-01-20, issue #8327, reported and test case by Constantine Theocharis
-- Pattern matching between fields is checked as an ordinary function.
-- In particular, eliminating Prop into Prop is allowed here.

{-# OPTIONS --prop #-}

-- {-# OPTIONS -v tc.prop:80 #-}
-- {-# OPTIONS -v tc.term.let.pattern:10 #-}
-- {-# OPTIONS -v tc.lhs:30 #-}

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
   refl : x ≡ x

record Foo (A : Set) : Set where
  field
    bar : A → A

  baz : (a : A) → a ≡ a → bar a ≡ bar a
  baz a refl = refl
  field
    bar' : A
