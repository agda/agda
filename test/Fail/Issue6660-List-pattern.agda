-- Lawrence, 2023-06-19, issue #6660

open import Agda.Builtin.Nat

record List (A : Set) : Set where
  inductive; no-eta-equality; pattern   -- disables co-pattern matching
  constructor _∷_
  field head : A
        tail : List A
open List

{-# INLINE _∷_ #-} -- expected to fail
