{-# OPTIONS --guardedness #-}
module CoinductiveUnitRecord where

open import Agda.Builtin.Equality

record Unit : Set where
  coinductive
  constructor delay
  field force : Unit
open Unit

good : Unit
force good = good

-- Andreas, Lawrence, 2023-05-26, issue #6660:
-- Now that coinductive constructor rhss are translated to copattern matching,
-- the following definitions are terminating, but no longer exact equations.

bad : Unit
bad = delay bad
-- WAS: should not termination check ...

bad' : Unit
bad' = delay bad'

-- WAS: ... because this loops:
loop : bad ≡ bad'
loop = refl

-- NOW:
-- bad != bad' of type Unit
-- when checking that the expression refl has type bad ≡ bad'
