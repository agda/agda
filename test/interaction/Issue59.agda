{-# OPTIONS -v term.inline:20 #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)

data [_] : Nat → Set where
  ⟨_⟩ : ∀ n → [ n ]


f : Nat → Nat
g : Nat → Nat
h : ∀ n → [ f n ]

f zero = zero
f (suc n) with f n
f (suc n) | zero  = zero
f (suc n) | suc m = f n + m

-- f's with-function should not get inlined into the clauses of g!
g zero = zero
g (suc n) = _   -- f (suc n) | f n

h zero = ⟨ zero ⟩
h (suc n) = ⟨ g (suc n) ⟩
