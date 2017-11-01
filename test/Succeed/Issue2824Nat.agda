-- Andreas, 2017-11-01, issue #2824
-- allow built-in pragmas in parametrized modules

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

module M (A : Set) where

  {-# BUILTIN NATURAL Nat #-}

  test = 5
