
open import Agda.Builtin.Nat

bar : Nat → Nat
bar n = let _!_ : Nat → Nat → Nat
            x ! y = 2 * x ! y  -- should give scope error in RHS
        in n ! n
