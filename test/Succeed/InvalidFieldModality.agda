-- Andreas, 2025-05-03, warn about ignored field attributes.

{-# OPTIONS --cohesion #-}
{-# OPTIONS --polarity #-}

record R : Set₁ where
  field
    @♭      f1 : Set -- warning FixingCohesion
    @-      f2 : Set -- warning FixingPolarity
    @+      f3 : Set -- warning FixingPolarity
    @++     f4 : Set -- warning FixingPolarity
    @unused f5 : Set -- warning FixingPolarity
    @mixed  ok : Set -- no warning!
