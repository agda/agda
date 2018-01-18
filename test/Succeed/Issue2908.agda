
open import Agda.Builtin.Nat
open import Agda.Builtin.Strict

foo : Nat → Nat
foo n = primForce (n + n) (λ _ → 0)
      -- Don't get rid of the seq!
