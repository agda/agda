-- Check that the termination checker can handle recursive
-- calls on subterms which aren't simply variables.
module SubtermTermination where

data N : Set where
  zero : N
  suc  : N → N

f : N → N
f (suc zero) = f zero
f _          = zero

data One? : N → Set where
  one : One? (suc zero)
  other : ∀ {n} → One? n

-- Should work for dot patterns as well
f′ : (n : N) → One? n → N
f′ (suc .zero) one = f′ zero other
f′ _           _   = zero

f″ : (n : N) → One? n → N
f″ ._ one = f″ zero other
f″ _  _   = zero

data D : Set where
  c₁ : D
  c₂ : D → D
  c₃ : D → D → D

g : D → D
g (c₃ (c₂ x) y) = g (c₂ x)
g _ = c₁

{- Andreas, 2011-07-07 subterm is not complete
   does not work with postulates or definitions

postulate
  i : {A : Set} → A → A

data NAT : N → Set where
  Zero : NAT zero
  Suc  : ∀ n → NAT (i n) → NAT (suc (i n))

h : (n : N) -> NAT n -> Set
h .zero Zero = N
h .(suc (i n)) (Suc n m) = h (i n) (i m)
-}