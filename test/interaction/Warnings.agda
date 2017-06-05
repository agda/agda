module Warnings where

-- empty rewrite pragma
{-# REWRITE #-}

-- termination checking error
A : Set
A = A

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

-- deprecated BUILTIN ZERO
{-# BUILTIN ZERO zero #-}

-- An open goal
g : Set
g = {!!}
