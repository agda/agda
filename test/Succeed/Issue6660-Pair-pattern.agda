-- Lawrence, 2023-06-19, issue #6660

open import Agda.Builtin.Nat

record Pair (A B : Set) : Set where
  inductive; no-eta-equality; pattern   -- disables co-pattern matching
  constructor _,_
  field fst : A
        snd : B
open Pair

{-# INLINE _,_ #-} -- expected to fail
