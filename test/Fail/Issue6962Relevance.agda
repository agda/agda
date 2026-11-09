module Issue6962Relevance where

open import Agda.Builtin.Nat

-- Interpreting a dotted atom as a parameter must check its annotations.
bad .(@relevant n : Nat) : Nat
bad = zero
