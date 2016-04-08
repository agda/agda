-- {-# OPTIONS -v tc.size.solve:60 #-}

module Issue300 where

open import Common.Size

data Nat : Size → Set where
  zero : (i : Size) → Nat (↑ i)
  suc  : (i : Size) → Nat i → Nat (↑ i)

-- Size meta used in a different context than the one created in

A : Set₁
A = (Id : (i : Size) → Nat _ → Set)
    (k : Size) (m : Nat (↑ k)) (p : Id k m) →
    (j : Size) (n : Nat j    ) → Id j n
-- should solve _ with ↑ i

-- 1) Id,k,m |- ↑ 1 ≤ X 1      ==> ↑ 4 ≤ X 4
-- 2) Id,k,m,p,j,n |- 1 ≤ X 1

-- Unfixed by fix for #1914 (Andreas, 2016-04-08).
