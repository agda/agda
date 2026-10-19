module Issue8596a where

open import Agda.Builtin.Nat

record P : Set where
  field fst snd : Nat
open P

p : P
p .fst = p .snd
p .snd = p .fst
-- should not termination-check
