module Issue8596b where

open import Agda.Builtin.Nat

record R : Set where
  field fst : Nat
open R

mutual
  use : R → Nat
  use x = x .fst

  r : R
  r .fst = use r
