
module A where

  Nat  : Set
  zero : Nat
  suc  : Nat -> Nat

  module Ind (P : Nat -> Set) where

    base : P zero
    step : (n : Nat) -> P n -> P (suc n)

  module Id (A : Set) where

    id : A -> A = \x -> x

    module Foo (x : A) where
      const : (B : Set) -> B -> A
	    = \B -> \b -> x

  module NatId = Id Nat

  module Id' (X : Set) = Id X

