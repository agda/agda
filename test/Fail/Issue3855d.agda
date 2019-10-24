postulate
  P    : Set → Set
  p    : (A : Set) → P A
  @0 A : Set

-- fails : P A
-- fails = p A

works : P A
works = p _
