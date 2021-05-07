-- Andreas, 2021-04-22, issue #5339
-- Allow constructors of the same name in `constructor` block.

module _ where

module Works where

  interleaved mutual
    data Nat : Set
    data Fin : Nat → Set
    data _ where
      zero : Nat
    data _ where
      suc  : Nat → Nat
      zero : ∀ {n} → Fin (suc n)
    data _ where
      suc : ∀ {n} (i : Fin n) → Fin (suc n)

interleaved mutual
  data Nat : Set
  data Fin : Nat → Set
  data _ where
    zero : Nat
    suc  : Nat → Nat
    zero : ∀ {n} → Fin (suc n)
    suc  : ∀ {n} (i : Fin n) → Fin (suc n)

-- `data _ where` block should be accepted despite duplicate constructor names.

wkFin : ∀{n} → Fin n → Fin (suc n)
wkFin zero    = zero
wkFin (suc i) = suc (wkFin i)
