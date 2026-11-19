module Issue6962RelevanceShape where

open import Agda.Builtin.Nat

bad ..(@relevant n : Nat) : Nat
bad = zero
