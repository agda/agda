open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.List

macro
  `Nat : Term → TC ⊤
  `Nat hole = do
    ty ← inferType hole
    _  ← debugPrint "tactic" 10 (termErr ty ∷ [])
    unify hole (def (quote Nat) [])

boom : `Nat
boom = 1
