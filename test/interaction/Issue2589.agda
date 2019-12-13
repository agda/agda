
open import Agda.Builtin.Nat

-- splitting on a 'with' argument should not expand the ellipsis
foo : Nat → Nat
foo m with 0
... | n = {!n!}

-- splitting on variable hidden by ellipsis should expand the ellipsis
bar : Nat → Nat
bar m with 0
... | n = {!m!}

-- test case with nested with
baz : Nat → Nat
baz m with m
... | n with n
... | p = {!p!}
