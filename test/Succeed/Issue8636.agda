-- Jesper, 2026-08-05, issue #8636 reported by Soares
-- Internal error when an instance value is used as an index.

record ⊤ : Set where constructor tt

record HasSection {A : Set} (B : A → Set) : Set where
  field section : (a : A) → B a
open HasSection {{...}}

record Fam1 (A : ⊤) : Set where
record Fam2 (x : Fam1 tt) : Set where

instance
  HasSection[Fam1] : HasSection Fam1
  HasSection[Fam1] .section _ = record {}

  HasSection[Fam2] : HasSection Fam2
  HasSection[Fam2] .section _ = record {}

crash : Fam2 (section tt)
crash = section (section _)
