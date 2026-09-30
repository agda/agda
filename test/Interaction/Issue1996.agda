{-# OPTIONS --no-keep-pattern-variables #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

test : (x : Nat) (f : {n : Nat} → Nat) → f {0} ≡ x → Nat
test x f p = {!p!}
