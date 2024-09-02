-- Andreas, 2024-02-20, issue #7136:
-- Error out on unsupported pattern synonym arguments.

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

nothing : Term → TC ⊤
nothing hole = returnTC _

pattern p {@(tactic nothing) x} = suc x

-- Should complain about tactics not being allowed in pattern synonyms
