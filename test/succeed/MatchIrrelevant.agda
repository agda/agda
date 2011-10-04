-- Andreas, 2011-10-03 
-- allow matching on irrelevant data as long as there is at most one
-- matching constructor
{-# OPTIONS --experimental-irrelevance #-}
module MatchIrrelevant where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data NAT : Nat -> Set where
  Zero : NAT zero
  Suc  : (n : Nat) -> NAT n -> NAT (suc n)

-- should succeed:
f : (n : Nat).(N : NAT n) -> Nat
f zero Zero = zero
f (suc n) (Suc .n N) = f n N

-- prove the equations to test reduction

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

fzero : f zero Zero ≡ zero
fzero = refl

fsuc : (n : Nat)(N : NAT n) -> f (suc n) (Suc n N) ≡ f n N
fsuc n N = refl

{- DOES NOT YET WORK and probably should never work
fzero' : (N : NAT zero) → f zero N ≡ zero
fzero' N = refl
-}

{-
-- should fail:
f' : (n : Nat).(N : NAT n) -> Nat
f' zero Zero = zero
f' (suc _) (Suc n N) = n
-}

{-
-- should fail:
g : {n : Nat}.(N : NAT n) -> Nat
g Zero = zero
g (Suc _ N) = g N
-}

{-
data Fin : Nat -> Set where
  zero : (n : Nat) -> Fin (suc n)
  suc  : (n : Nat) -> Fin n -> Fin (suc n)


-- should fail:
toNat : {n : Nat} → .(Fin n) -> Nat
toNat (zero n) = zero
toNat (suc n i) = suc (toNat i)
-}

{-
-- fails for other reasons
weak : {n : Nat} → .(Fin n) -> Fin (suc n)
weak (zero n) = zero (suc n)
weak (suc n i) = suc (suc n) (weak i)
-}