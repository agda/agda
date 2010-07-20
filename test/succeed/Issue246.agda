module Issue246 where

-- Example from James & Varmo (edited).

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Zero : Set where

data One : Set where
  void : One

propLEQ : Nat → Nat → Set
propLEQ zero    _       = One
propLEQ (suc n) (suc m) = propLEQ n m
propLEQ (suc n) zero    = Zero

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

toFin : {n : Nat} → (i : Nat) → (propLEQ (suc i) n) → Fin n
toFin {zero}  zero      ()
toFin {zero}  (suc _)   ()
toFin {suc n} zero    k  = fzero
toFin {suc n} (suc i) k  = fsuc (toFin i k)

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

null : Fin three
null = toFin zero void

-- Example from Conor (edited).

data Bool : Set where
 tt ff : Bool

So : Bool → Set
So tt = One
So ff = Zero

_<_ : Nat → Nat → Bool
_ < zero = ff
zero < suc n = tt
suc m < suc n = m < n

data Lt (m n : Nat) : Set where
 lt : So (m < n) → Lt m n

boo : {m n : Nat} → So (m < n) → Lt (suc m) (suc n)
boo p = lt p
