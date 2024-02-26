-- Andreas, 2024-02-26, issue #7148 brings back #1342.
-- We are not supposed to match on a module parameter,
-- even when it is given in eta-expanded form.

open import Agda.Builtin.Equality

data One : Set where
  one : One

record Wrap (A : Set) : Set where
  constructor wrap
  field wrapped : A
open Wrap

Unit = Wrap One
pattern unit = wrap one

id : (A : Set) → A → A
id A a = a

module Works where

  dx : (x : Unit) → Unit → Unit
  dx x unit = x

  g : (x : Unit) → ∀ u → x ≡ dx x u
  g x with wrap (wrapped x)
  g x | unit = id ((u : Unit) → unit ≡ dx unit u) {!!}

-- Now if we make (x : Unit) a module parameter
-- then we turn all applications (dx _) into just dx,
-- which actually means (dx x), i.e., dx applied to
-- the module free variables.

-- This leads to an incomprehendable rejection
-- of the following code (culprit is the first argument to id).

module M (x : Unit) where

  dx : Unit → Unit
  dx unit = x

  g : ∀ u → x ≡ dx u
  -- As well as rejecting `with x` we should also
  -- reject `with (eta-expansion-of x)`.
  g with wrap (wrapped x)
  g | unit  = id ((u : Unit) → unit ≡ dx u) ?

-- Error WAS:
--
-- wrapped x != one of type One
-- when checking that the inferred type of an application
--   (u : Unit) → unit ≡ dx u
-- matches the expected type
--   (u : Wrap One) → unit ≡ dx u
--
-- Expected error NOW:
--
-- Cannot `with` on expression wrap (wrapped x) which reduces to
-- variable x bound in a module telescope (or patterns of a parent clause)
-- when inferring the type of wrap (wrapped x)

-- -}
