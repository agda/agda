
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Reflection

postulate
  tac : {A : Set} (x : A) → Term → TC ⊤

data D : Set where
  con : {@(tactic tac true) y : Bool} → D

-- WAS: Internal error in Serialize/Instances/Internal for MetaV case
-- SHOULD: succeed
