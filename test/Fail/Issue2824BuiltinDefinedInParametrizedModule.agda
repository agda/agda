-- Andreas, 2017-11-01, issue #2824
-- Don't allow built-ins defined in parametrized modules

module _ (A : Set) where

  data Nat : Set where
    zero : Nat
    suc : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}  -- Should fail

  test = 5
