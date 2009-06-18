
module Issue168 where

postulate X : Set

open import Issue168b
open Membership X

postulate
  P : Nat → Set
  lemma : ∀ n → P (id n)

foo : P zero
foo = lemma _
