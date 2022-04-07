
-- Reported by matteo.acerbi, AIMXX, 2014-10-21

-- The following is accepted.

{-# OPTIONS --guardedness #-}
{-# OPTIONS --cubical-compatible  #-}

-- {-# OPTIONS -v term:30 #-}

record X : Set where
  coinductive
  constructor ↑_
  field       ↓_ : X
open X

record Y (x1 x2 : X) : Set where
  coinductive
  field       ]_[ : Y (↑ x1) (↑ x2)
open Y

trivial-Y : ∀ {x1 x2} → Y x1 x2
] trivial-Y [ = trivial-Y

-- Should termination check.
