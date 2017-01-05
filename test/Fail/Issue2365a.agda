open import Agda.Builtin.Nat

-- Matching against negative numbers

lit : Nat → Nat
lit -20 = 0  -- Error thrown here
lit _   = 1
