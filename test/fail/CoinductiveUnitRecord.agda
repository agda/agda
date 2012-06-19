{-# OPTIONS --copatterns #-}
module CoinductiveUnitRecord where

import Common.Level
open import Common.Equality

record Unit : Set where
  coinductive
  constructor delay
  field force : Unit
open Unit

good : Unit
force good = good

bad : Unit
bad = delay bad
-- should not termination check ...

bad' : Unit
bad' = delay bad'

-- ... because this loops:
-- loop : bad ≡ bad'
-- loop = refl

