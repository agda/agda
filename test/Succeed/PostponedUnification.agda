
{-  This example test that the order in which unification
    constraints are generated doesn't matter. The pattern
    matching in foo generates the unification problem
      [x, zero] = [n + m, n]
    with n and m flexible. The first equation can only be
    solved after the second one has been solved. For completeness
    we check that the other way around also works.
-}
module PostponedUnification where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

data T : Nat -> Nat -> Set where
  t  : (x : Nat) -> T x zero

foo : (n m : Nat) -> T (n + m) n -> Set
foo ._ ._ (t x) = Nat

data U : Nat -> Nat -> Set where
  u  : (x : Nat) -> U zero x

bar : (n m : Nat) -> U n (n + m) -> Set
bar ._ ._ (u x) = Nat

