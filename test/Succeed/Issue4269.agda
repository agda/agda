-- Reported by Christian Sattler on 2019-12-07

open import Agda.Primitive

postulate
  i : Level
  X : Set i

mutual
  j : Level
  j = _

  Y : Set j
  Y = X

-- WAS: unsolved constraint i = _2
-- SHOULD: succeed with everything solved
