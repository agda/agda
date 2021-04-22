-- Andreas, 2021-04-22, issue #5339
-- Allow constructors of the same name in `constructor` block.

module _ where

module Works where

  interleaved mutual
    data Nat : Set
    data Fin : Nat → Set
    constructor
      zero : Nat
    constructor
      suc  : Nat → Nat
      zero : ∀ {n} → Fin (suc n)
    constructor
      suc : ∀ {n} (i : Fin n) → Fin (suc n)

interleaved mutual
  data Nat : Set
  data Fin : Nat → Set
  constructor
    zero : Nat
    suc  : Nat → Nat
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} (i : Fin n) → Fin (suc n)

-- `constructor` block should be accepted despite duplicate constructor names.

wkFin : ∀{n} → Fin n → Fin (suc n)
wkFin zero    = zero
wkFin (suc i) = suc (wkFin i)
