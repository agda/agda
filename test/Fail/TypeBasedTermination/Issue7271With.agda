-- Andreas, 2024-05-16, issue #7271.
-- Bug in size-preservation checker.

{-# OPTIONS --type-based-termination #-}

module TypeBasedTermination.Issue7271With where

data ⊥ : Set where

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B
open _×_

-- Empty stream type.
--
record S : Set where
  coinductive; constructor delay
  field force : ⊥ × S
open S

-- This is not size-preserving:
--
f : S → ⊥ × S
f s with s
... | s' = s' .force

-- This should not be accepted:
--
s : S
s .force = f s

absurd : ⊥
absurd = s .force .fst
