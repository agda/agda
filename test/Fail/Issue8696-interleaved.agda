-- Andreas, 2026-08-29, issue #8696
-- Issue found by Claude and reported by bdrisc-ant
-- This is the original reproducer "A".

-- A module application creates, for each data or record type of the applied
-- module, a copy that is defined by the pattern-less clause  N.F = M.F ⊥.
-- If the application happens while a mutual block is open, the copy is a
-- member of that block and its argument occurrences are recomputed.  Since
-- the copy's clause has no patterns for the parameters of N.F, the analysis
-- used to find no occurrence of them and overwrite the (correct) inherited
-- occurrences by Unused.  A later data type could then be negative through the
-- copy without the positivity checker noticing.

{-# OPTIONS --safe --without-K #-}

data ⊥ : Set where

module M (A : Set) where

  -- X occurs both positively and negatively in F: its occurrence is Mixed.
  data F (X : Set) : Set where
    neg : (X → A) → F X
    pos : X → F X

-- The module application lands inside Dummy's mutual block
-- (here: between an interleaved signature and its definition).
data Dummy : Set
module N = M ⊥
data Dummy where
  mkD : Dummy

-- A later block: G wraps the copy, Bad is negative through it.
G : Set → Set
data Bad : Set
G X = N.F X
data Bad where
  bad : G Bad → Bad

¬Bad : Bad → ⊥
¬Bad (bad (N.neg f)) = f (bad (N.neg f))
¬Bad (bad (N.pos b)) = ¬Bad b

boom : ⊥
boom = ¬Bad (bad (N.neg ¬Bad))
