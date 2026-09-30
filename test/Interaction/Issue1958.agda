open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

test1 : Nat → Nat
test1 zero       = 0
test1 (suc zero) = 1
test1 (suc n)    = {!n!}

test2 : Nat → Nat → Nat
test2 zero zero    = zero
test2 zero (suc y) = y
test2 x    y       = {!x!}

test3 : Bool → Bool → Bool → Bool
test3 true  true  true  = true
test3 x     true  false = x
test3 false y     true  = y
test3 true  false z     = z
test3 x     y     z     = {!x y z!}
