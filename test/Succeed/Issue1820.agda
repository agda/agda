{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Nat

test : (n : Nat) → Nat
test n with zero
... | n = {!n!}
