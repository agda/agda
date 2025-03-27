{-# OPTIONS --prop #-}

open import Agda.Primitive

data Natω : Setω where
  zero : Natω
  suc  : Natω → Natω

data SqNatω : Propω where
  sq : Natω → SqNatω

unsq : SqNatω → Natω
unsq (sq n) = n

-- Expected error: [SplitInProp]
-- Cannot split on datatype in Prop unless target is in Prop
-- when checking that the pattern sq n has type SqNatω
