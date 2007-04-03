
module Top where

module A where

  Nat  : Set
  zero : Nat
  -- suc  : Nat -> Nat

  module Q where
    module R where
      f : Nat -> Nat = \x -> zero

  module B (n : Nat) where
    open Q.R
    q : Nat = n

  n : Nat = B.f zero zero

--  module Bz = B zero renaming (q to r)

--  m : Nat = B.q zero

{-
  module B (n : Nat) where
    module C (m : Nat) where
      q : Nat = m
    z : Nat = zero

  module D = B zero renaming (module C to C')
  module E = D.C' (suc zero) renaming (q to m')

  q : Nat = E.m'
-}
{-
  module B (n : Nat) where
    m : Nat = n

  module Z = B zero

  z : Nat = Z.m

  module C where
    f : Nat -> Nat

  module D where
    open C
    g : Nat -> Nat = f

  module Ind (P : Nat -> Set) where

    base : P zero
    step : (n : Nat) -> P n -> P (suc n)

  module Id (A : Set) where

    id : A -> A = \x -> x

    module Foo (x : A) where
      const : (B : Set) -> B -> A
	    = \B -> \b -> x

  module NatId = Id Nat

  module Q where
    module Foo' (X : Set)(x : X) = Id.Foo X x

  open NatId

  z : Nat = id zero
-}
