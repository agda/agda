-- Andreas, 2026-08-28, while working on issue #8699.
-- Status quo: Prop dot pattern accepted even if it does not "make sense".

{-# OPTIONS --prop --show-irrelevant #-}

data N : Prop where
  zero : N
  suc : (n : N) → N

data D : N → Set where
  c : (m : N) → D (suc m)

f : (n : N) → D n → Set₁
f .(suc m) (c m) = Set

-- The following dot pattern are also accepted even though
-- they are not literally the expected one, namely `suc m`,
-- because all `N`s are equal (is a Prop).

g : (n : N) → D n → Set₁
g .(suc (suc m)) (c m) = Set

h : (n : N) → D n → Set₁
h  .zero (c m) = Set

-- Should succeed.
