open import Agda.Builtin.Nat

lit : Nat → Set
lit 5 with 0
lit 3 | _ = Nat
lit _ = Nat
