
open import Agda.Builtin.Nat
open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit

instance
  NumberNat : Number Nat
  Number.Constraint NumberNat _ = ⊤
  fromNat {{NumberNat}} n = n

open import Issue2641.Import
