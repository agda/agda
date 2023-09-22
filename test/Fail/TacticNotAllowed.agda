-- Andreas, 2023-08-23, re PR #6777
-- Trigger error "The @tactic attribute is not allowed here".
-- Should highlight exactly the attribute.

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

nothing : Term → TC ⊤
nothing hole = returnTC _

module M (A : Set) {@(tactic nothing) f : A → A} where
  -- The following code is only to make the module bigger.
  -- Originally, the whole module was highlighted.
  postulate
    a : A
  b = f a

-- Expected error:
-- The @tactic attribute is not allowed here
--
-- Exactly the tactic attribute should be highlighted.
