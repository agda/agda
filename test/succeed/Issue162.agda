-- Now you don't need a mutual keyword anymore!
module Issue162 where

data Odd : Set
data Even : Set where
  zero : Even
  suc  : Odd → Even

data Odd where
  suc : Even → Odd

-- This means you can have all kinds of things in
-- mutual blocks.

-- Like postulates
_o+e_ : Odd → Even → Odd

_e+e_ : Even → Even → Even
zero e+e m = m
suc n e+e m = suc (n o+e m)

postulate todo : Even

suc n o+e m = suc todo

-- Or modules
_e+o_ : Even → Odd → Odd
_o+o_ : Odd → Odd → Even
suc n o+o m = suc (n e+o m)

module Helper where
  f : Even → Odd → Odd
  f zero    m = m
  f (suc n) m = suc (n o+o m)

n e+o m = Helper.f n m

-- Multiplication just for the sake of it
_o*o_ : Odd → Odd → Odd
_e*o_ : Even → Odd → Even
zero  e*o m = zero
suc n e*o m = m o+o (n o*o m)

suc n o*o m = m o+e (n e*o m)
