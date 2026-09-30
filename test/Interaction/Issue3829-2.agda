open import Agda.Builtin.Nat

-- split on m

-- WAS: m = zero or m = suc m
-- WANT: m = suc m because 2nd clause already covers m = zero

f : Nat -> Nat -> Nat
f m zero = {!!}
f zero zero = zero
f _ _ = zero

-- However for g, we still get m = zero or m = suc m
-- because the other splits are orthogonal / catchalls

g : Nat -> Nat -> Nat
g m zero = {!!}
g zero n = zero
g _ _ = zero
