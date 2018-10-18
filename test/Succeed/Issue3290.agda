
module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

variable
  f : Nat → Nat

-- Drops the argument to f!
foo : (n : Nat) → f n ≡ n → f (f n) ≡ n
foo n eq rewrite eq = eq
