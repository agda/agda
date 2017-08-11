
data Bool : Set where
  true false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

one : Nat
one = suc zero

two : Nat
two = suc one

data Fin : Nat → Set where
  zero : ∀{n} → Fin (suc n)
  suc  : ∀{n} (i : Fin n) → Fin (suc n)

--This part works as expected:

s : ∀ n → (f : (k : Fin n) → Bool) → Fin (suc n)
s n f = zero

t1 : Fin two
t1 = s one (λ { zero → true ; (suc ()) })

-- But Agda is not able to infer the 1 in this case:

ttwo : Fin two
ttwo = s _ (λ { zero → true ; (suc ()) })

-- Warning:
-- _142 : Nat

-- The problem gets worse when i add arguments to the ttwo function. This gives an error:

t3 : Set → Fin two
t3 A = s _ (λ { zero → true ; (suc ()) })
