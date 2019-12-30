-- Reported by Christian Sattler on 2019-12-7

postulate
  A B : Set

barb : Set
barb = (A → (_ : B) → _) _

-- WAS: unsolved constraints.
-- SHOULD: throw an error that A → ... is not a function.
