
module _ where

postulate
  I : Set

data P (i : I) : Set where
  p : P i → P i

data Q (i : I) : P i → Set where
  q : (x : P i) → Q i (p x)

module _ (i : I) (x : P i)  where
  g : Q _ x → Set₁
  g (q y) = Set
