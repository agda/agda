data Nat : Set where
  zero : Nat
  suc : Nat → Nat

test : ∀{N M : Nat} → Nat → Nat → Nat
test L K = {!N L M!}
-- Andreas, 2016-07-10, issue 2088
-- Changed behavior:
-- The hidden variables N and M are made visible
-- only the visible L is split.
