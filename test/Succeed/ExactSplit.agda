{-# OPTIONS --exact-split #-}

-- The --exact-split flag causes Agda to raise an error whenever
-- a clause in a definition by pattern matching cannot be made to
-- hold definitionally (i.e. as a reduction rule). Specific clauses
-- can be excluded from this check by means of the {-# CATCHALL #-}
-- pragma.

module ExactSplit where

data Bool : Set where
  true false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# CATCHALL #-}  -- InvalidCatchallPragma, ignored
_+_ : ℕ → ℕ → ℕ
zero    + n    = zero
(suc m) + n    = suc (m + n)
{-# CATCHALL #-}  -- InvalidCatchallPragma, ignored

eq : ℕ → ℕ → Bool
eq zero    zero    = true
eq (suc m) (suc n) = eq m n
{-# CATCHALL #-}
{-# CATCHALL #-}  -- InvalidCatchallPragma, ignored
eq _       _       = false

-- See also fail/ExactSplitMin.agda
min : ℕ → ℕ → ℕ
min zero    y       = zero
{-# CATCHALL #-}
min x       zero    = zero
min (suc x) (suc y) = suc (min x y)

-- See also fail/ExactSplitBerry.agda
maj : Bool → Bool → Bool → Bool
maj true  true  true  = true
{-# CATCHALL #-}
maj x     true  false = x
{-# CATCHALL #-}
maj false y     true  = y
maj true  false z     = z
maj false false false = false

-- See also fail/ExactSplitParity.agda
parity : ℕ → ℕ → Bool
parity zero          zero          = true
parity zero          (suc zero)    = false
parity zero          (suc (suc n)) = parity zero n
parity (suc zero)    zero          = false
parity (suc (suc m)) zero          = parity m zero
{-# CATCHALL #-}
parity (suc m)       (suc n)       = parity m n
