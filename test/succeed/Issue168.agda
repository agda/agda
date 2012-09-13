{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.polarity:10 -v tc.inj:40 -v tc.conv.irr:20 #-}  -- -v tc.mod.apply:100 #-}
module Issue168 where

postulate X : Set

open import Issue168b
open Membership X

postulate
  P : Nat → Set
  lemma : ∀ n → P (id n)

foo : P zero
foo = lemma _
