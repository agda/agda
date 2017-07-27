-- Andreas, 2017-07-26
-- Better error message when constructor not fully applied.

open import Agda.Builtin.Nat

test : (Nat → Nat) → Nat
test suc = suc zero

-- WAS: Type mismatch
-- NOW: Cannot pattern match on functions
-- when checking that the pattern suc has type Nat → Nat
