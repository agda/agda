-- {-# OPTIONS -v tc.lhs:100 #-}

module IrrelevantData where

data T (A : Set) : Set where
  c : .A → T A

d : ∀ {A} → T A → A
d (c x) = x
-- needs to fail since x is irrelevant under c