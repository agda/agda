
module ShouldBeAppliedToTheDatatypeParameters where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

mutual

  F : Nat -> Set
  F zero    = Nat
  F (suc n) = Foo (F n)

  data Foo (A : Set) : Set where
    fooI1 : F (suc zero)

