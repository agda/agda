------------------------------------------------------------------------
-- Some properties about natural number operations
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Nat.Properties.

module Data.Nat.Properties.Core where

open import Data.Nat.Core
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; byDef to ≤-refl)
open import Data.Function

n≤1+n : forall n -> n ≤ 1 + n
n≤1+n zero    = z≤n
n≤1+n (suc n) = s≤s $ n≤1+n n

n≤m+n : forall m n -> n ≤ m + n
n≤m+n zero    n = ≤-refl
n≤m+n (suc m) n =
             start
  n
             ≤⟨ n≤m+n m n ⟩
  m + n
             ≤⟨ n≤1+n _ ⟩
  1 + m + n
             □
