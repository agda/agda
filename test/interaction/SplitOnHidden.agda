data Nat : Set where
  zero : Nat
  suc : Nat → Nat

test : ∀{N M : Nat} → Nat → Nat → Nat
test N M = {!.N N .M!}
