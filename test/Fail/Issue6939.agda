-- Andreas, 2025-08-08, issue #6939, report and test by Jesper Cockx

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Reflection

macro
  run : (Term → TC ⊤) → Term → TC ⊤
  run f hole = f hole

auto : Term → TC ⊤
auto hole = unify hole (var 0 [])

postulate
  doTheThing : @(tactic auto) {Set} → Set        -- warning
  doTheThingToo : {@(tactic auto) _ : Set} → Set

postulate
  works     : (x : Set) → doTheThing {run auto}
  alsoWorks : (x : Set) → doTheThingToo
  fails     : (x : Set) → doTheThing

-- warning: -W[no]MisplacedAttributes
-- Ignoring misplaced @(tactic ...) attribute
