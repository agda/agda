-- Andreas, 2017-08-25, issue #1611.
-- Fixed by Jesper Cockx as #2621.

open import Common.Prelude

data D : Bool → Set where
  dt : D true
  df : D false

Works : ∀{b} → D b → Set
Works dt = Bool
Works df = Bool

Fails : ∀{b : Bool} → D _ → Set
Fails dt = Bool
Fails df = Bool

-- WAS:
-- false != true of type Bool
-- when checking that the pattern df has type D true

-- SHOULD BE:
-- Don't know whether to split on dt

-- NOW:
-- I'm not sure if there should be a case for the constructor dt,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   true ≟ _9
-- when checking that the pattern dt has type D _9
