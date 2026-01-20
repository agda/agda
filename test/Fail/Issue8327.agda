-- Andreas, 2026-01-20, issue #8327, reported and test case by Constantine Theocharis
-- Pattern-matching definitions inbetween fields of a record declaration
-- may only contain record patterns, so we expect errors to that extend.
-- In the present case, SplitInProp was raised, however.
-- This was due to the fact that the LHS checker ran before the check that
-- the patterns are actually record patterns.

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
     -- ^ Error was: [SplitInProp] Cannot split on datatype in Prop unless target is in Prop
     --   Expected error: [ShouldBeRecordPattern] Expected record pattern
  field
    bar' : A
