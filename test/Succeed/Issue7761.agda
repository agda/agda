-- Andreas, 2025-03-27, issue #7761, reported and test by Szumi Xie
-- Propω should also be proof irrelevant.

{-# OPTIONS --prop #-}

open import Agda.Primitive

postulate
  A : Propω
  x y : A
  P : A → Set

test : P x → P y
test p = p

-- Andreas, 2025-03-27
-- Allow propositional squashing also in Propω.

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- Small positional squashing.

data SqNat : Prop where
  sq : Nat → SqNat

-- Large positional squashing.

data Natω : Setω where
  zero : Natω
  suc  : Natω → Natω

data SqNatω : Propω where
  sq : Natω → SqNatω

succ : SqNatω → SqNatω
succ (sq n) = sq (suc n)
