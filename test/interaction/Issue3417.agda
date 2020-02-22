-- Andreas, 2019-02-17, issue #3417
--
-- We want to see highlighting for all the warnings,
-- even if the last thing is a hard error.

open import Agda.Builtin.Nat

reachable : Nat → Nat
reachable zer = 0
reachable (suc n) = suc (reachable n)

coverage : Nat → Nat
coverage zero = zero

Termination : Set
Termination = Termination

data Positivity : Set where
  abs : (Positivity → Nat) → Positivity

Universe : Set
Universe = Set

-- Problem was: Termination and Positivity got no highlighting.
