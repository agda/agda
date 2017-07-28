-- Andreas, 2017-07-28, issue #1126 reported by Saizan is fixed

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ
{-# BUILTIN NATURAL ℕ #-}

data Unit : Set where
  unit : Unit

slow : ℕ → Unit
slow zero = unit
slow (suc n) = slow n

postulate
  IO : Set → Set
{-# COMPILE GHC IO = type IO #-}
{-# BUILTIN IO IO #-}

postulate
  return  : ∀ {A} → A → IO A
{-# COMPILE GHC return = (\ _ -> return) #-}
{-# COMPILE JS return =
    function(u0) { return function(u1) { return function(x) { return function(cb) { cb(x); }; }; }; } #-}

force : Unit → IO Unit
force unit = return unit

n = 3000000000

main : IO Unit
main = force (slow n)

-- Should terminate instantaneously.
