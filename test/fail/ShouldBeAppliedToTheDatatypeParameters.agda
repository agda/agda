
module ShouldBeAppliedToTheDatatypeParameters where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

mutual
  data Foo (A : Set) : Set

  F : Nat -> Set
  F zero    = Nat
  F (suc n) = Foo (F n)

  data Foo A where
    fooI1 : F (suc zero)

