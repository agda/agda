open import Agda.Builtin.Nat

-- split on m

-- WAS: m = zero or m = suc m
-- WANT: m = suc m because 2nd clause already covers m = zero

f : Nat -> Nat -> Nat
f m zero = {!!}
f zero n = zero
f _ _ = zero
