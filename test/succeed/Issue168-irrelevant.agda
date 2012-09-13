-- Andreas, 2012-09-13 respect irrelevance at meta-var creation
-- {-# OPTIONS -v tc.conv.irr:20 #-}
module Issue168-irrelevant where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

module Id .(A : Set) where
  id : Nat → Nat
  id zero     = zero
  id (suc xs) = suc (id xs)
open Id Nat

postulate
  P : Nat → Set
  lemma : ∀ n → P (id n)

foo : P zero
foo = lemma _
