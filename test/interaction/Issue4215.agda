
open import Agda.Builtin.Nat

foo : Nat → Nat → Nat
foo 0 m = {!m!}
foo (suc n) m = {!!}
