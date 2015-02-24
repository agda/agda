-- Andreas, 2015-02-24

data N : Set where
  zero : N
  suc  : N → N

data Sing : (n : N) → Set where
  sing : ∀ n → Sing n

data D : Set → Set where
  c : ∀ n → D (Sing n)

test : (A : Set) → D A → N
test .(Sing n) (c n) = n

-- this should crash Epic as long as n is considered forced in constructor c

-- should succeed now
