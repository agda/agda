------------------------------------------------------------------------
-- Natural numbers (some core definitions)
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Nat.

module Data.Nat.Core where

------------------------------------------------------------------------
-- The types

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

infix 4 _≤_ _<_

data _≤_ : ℕ -> ℕ -> Set where
  z≤n : forall {n}            -> zero  ≤ n
  s≤s : forall {m n} -> m ≤ n -> suc m ≤ suc n

_<_ : ℕ -> ℕ -> Set
m < n = suc m ≤ n

------------------------------------------------------------------------
-- Some operations

infixl 6 _+_

_+_ : ℕ -> ℕ -> ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}
