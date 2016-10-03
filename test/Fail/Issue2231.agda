-- Andreas, 2016-10-01, issue #2231
-- The termination checker should not always see through abstract definitions.

abstract
  data Nat : Set where
    zero' : Nat
    suc'  : Nat → Nat

  -- abstract hides constructor nature of zero and suc.
  zero = zero'
  suc  = suc'

data D : Nat → Set where
  c1 : ∀ n → D n → D (suc n)
  c2 : ∀ n → D n → D n

-- To see that this is terminating the termination checker has to look at the
-- natural number index, which is in a dot pattern.
f : ∀ n → D n → Nat
f .(suc n) (c1  n d) = f n (c2 n (c2 n d))
f n        (c2 .n d) = f n d

-- Termination checking based on dot patterns should fail,
-- since suc is abstract.
