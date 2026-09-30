
open import Agda.Builtin.Nat

f : Nat → Nat
f v@n with n
... | zero = zero
... | suc m with m
...   | zero  = {!!}
...   | suc o with o
...     | zero  = {!!}
...     | suc p = {!!}
