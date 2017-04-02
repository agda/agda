module Golden.Constructor where

open import Agda.Builtin.Nat

f : (Nat -> Nat) -> Nat
f g = g zero

fsuc = suc
fzero = zero

one = f suc
a = fsuc fzero
