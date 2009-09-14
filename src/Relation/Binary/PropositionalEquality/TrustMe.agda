
module Relation.Binary.PropositionalEquality.TrustMe where

open import Relation.Binary.PropositionalEquality

private
 primitive
   primTrustMe : {A : Set}{a b : A} → a ≡ b

trustMe : {A : Set}{a b : A} → a ≡ b
trustMe = primTrustMe
