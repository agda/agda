-- Andreas, 2024-04-14
-- Trigger error "Cannot pattern match on non-constructor ..."
-- Renamed to InvalidPattern error.

open import Agda.Builtin.Nat as NAT

test : Nat → Nat
test zero = zero
test (suc NAT.Nat) = zero

-- Error WAS:
-- Cannot pattern match on non-constructor NAT.Nat
-- when ...
--
-- NOW:
-- NAT.Nat is not a valid pattern
-- when scope checking the left-hand side test (suc NAT.Nat) in the
-- definition of test
