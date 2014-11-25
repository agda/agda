{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc:10 #-}
-- {-# OPTIONS -v tc.with:40 #-}

-- Andreas, 2014-11-26
-- Reported by twanvl

data Unit : Set where
  unit : Unit

module Mod₁ (t : Unit) where
  postulate Thing : Set

module Mod₂ (u : Unit) where

  open Mod₁ unit

  record Foo : Set where
    field
      foo : Thing → Thing

    bar : Thing → Thing
    bar a with foo a
    ... | x = x

-- checkInternal stumbles over
--   (λ u₁ → Thing) {u} : Setω
-- which is an internal representation of Thing, to be precise
--   Mod₂._.Thing u  which expands to  Mod₁.Thing unit

-- More complete transcript:

-- checking internal  Thing  :  Setω
-- reduction on defined ident. in anonymous module
-- x = Issue1332.Mod₂._.Thing
-- v = Def Issue1332.Mod₁.Thing [Apply []r(Con Issue1332.Unit.unit(inductive)[] [])]

-- elimView of  Thing
-- v = Def Issue1332.Mod₂._.Thing [Apply []r{Var 1 []}]
-- reduction on defined ident. in anonymous module
-- x = Issue1332.Mod₂._.Thing
-- v = Def Issue1332.Mod₁.Thing [Apply []r(Con Issue1332.Unit.unit(inductive)[] [])]

-- elimView (projections reduced) of  Thing
-- reduction on defined ident. in anonymous module
-- x = Issue1332.Mod₂._.Thing
-- v = Lam (ArgInfo {argInfoHiding = NotHidden, argInfoRelevance = Relevant, argInfoColors = []}) (Abs "u" Def Issue1332.Mod₁.Thing [Apply []r(Con Issue1332.Unit.unit(inductive)[] [])])

-- checking spine
-- (
-- λ u₁ → Thing
--  :
-- (u₁ : Thing) → Set
-- )
-- [$ {u}]
--  :
-- Setω
-- /home/abel/agda/test/bugs/Issue1332.agda:23,5-24,16
-- Expected a visible argument, but found a hidden argument
-- when checking that the type (a : Thing) → Thing → Thing of the
-- generated with function is well-formed
