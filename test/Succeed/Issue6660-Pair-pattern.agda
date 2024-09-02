-- Lawrence, 2023-06-19, issue #6660
-- Andreas, 2024-06-01, issue #7301

open import Agda.Builtin.Nat

record Pair (A B : Set) : Set where
  inductive; no-eta-equality; pattern   -- disables co-pattern matching
  constructor _,_
  ------------------------------------------------------------------------
  -- Some extra directives that should trigger dead-code warnings (issue #7301)
  coinductive; eta-equality; no-eta-equality; pattern; inductive; constructor foo; constructor _,_
  ----------------------------------------------------------------------------------
  field fst : A
        snd : B
open Pair

{-# INLINE _,_ #-} -- #6660 expected to fail

-- #7301: expected warnings about extra record directives
