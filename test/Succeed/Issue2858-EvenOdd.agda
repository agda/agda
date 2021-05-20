data Nat : Set where
  zero : Nat
  suc : Nat → Nat

interleaved mutual

  data Even : Nat → Set
  data Odd  : Nat → Set

  -- base cases: 0 is Even, 1 is Odd
  data _ where
    even-zero : Even zero
    odd-one   : Odd (suc zero)

  -- step case: suc switches the even/odd-ness
  data _ where
    even-suc : ∀ {n} → Odd n → Even (suc n)
    odd-suc  : ∀ {n} → Even n → Odd (suc n)
