-- Andreas, 2013-02-27 issue reported by Nisse
-- {-# OPTIONS -v tc.polarity:100 -v tc.pos:100 #-}
module Issue802 where

data I : Set where
  i : I

mutual

  data P : I → Set where
    p : (x : I) → Q x x → P x

  Q : I → I → Set
  Q i = P
  -- Polarity of Q should be mixed for both arguments.

f : (x y : I) → Q x y → P y
f i _ q = q

data R (x : I) : P x → Set where
  r : (q : Q x x) → R _ (f x _ q) → R x (p x q)

-- Agda should solve the two meta variables in the type of r.
