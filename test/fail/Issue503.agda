-- div shouldn't termination check, but it also shouldn't make the termination
-- checker loop.
module Issue503 where

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {C : Set} -> Bool -> C -> C -> C
if true then a else b = a
if false then a else b = b

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

pred : Nat -> Nat
pred zero = zero
pred (succ n) = n

_+_ : Nat -> Nat -> Nat
zero + b = b
succ a + b = succ (a + b)

_*_ : Nat -> Nat -> Nat
zero * _ = zero
succ a * b = (a * b) + b

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC succ #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

_-_ : Nat -> Nat -> Nat
a - zero = a
a - succ b = pred (a - b)

_<_ : Nat -> Nat -> Bool
a < zero = false
zero < succ b = true
succ a < succ b = a < b

div : Nat -> Nat -> Nat
div m n = if (m < n) then zero else succ (div (m - n) n)
