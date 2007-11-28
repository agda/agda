
-- You can have infix declarations in records.

module InfixRecordFields where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

infixl 50 _+_
_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

one = suc zero
two = suc (suc zero)

record A : Set where
  field x   : Nat
        _*_ : Nat -> Nat -> Nat
        h   : (one + one * x) == one  -- later fields make use of the fixity
  infixl 60 _*_

a : A
a = record { x = zero; _*_ = \ x y -> y; h = refl }

open module X = A a

-- The projection functions also have the right fixity.
p : (one + one * zero) == one
p = refl

