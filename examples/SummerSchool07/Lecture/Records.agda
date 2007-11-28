{-

          Types Summer School 2007

                 Bertinoro
             Aug 19 - 31, 2007


                   Agda

                Ulf Norell

-}

-- Records are labeled sigma types.

module Records where

open import Nat
open import Bool

{-

  A very simple record.

-}

record Point : Set where
  field
    x : Nat
    y : Nat

-- A record can be seen as a one constructor datatype. In this case:
data Point' : Set where
  mkPoint : (x : Nat)(y : Nat) -> Point'

-- There are a few differences, though:

-- To construct a record you use the syntax record { ..; x = e; .. }
origin : Point
origin = record { x = 0; y = 0 }

-- instead of
origin' : Point'
origin' = mkPoint 0 0

-- What's more interesting is that you get projection functions
-- for free when you declare a record. More precisely, you get a module
-- parameterised over a record, containing functions corresponding to the
-- fields. In the Point example you get:
{-
  module Point (p : Point) where
    x : Nat
    y : Nat
-}

-- So Point.x : Point -> Nat is the projection function for the field x.
getX : Point -> Nat
getX = Point.x

-- A nifty thing with having the projection functions in a module is that
-- you can apply the module to a record value, in effect opening the record.
sum : Point -> Nat
sum p = x + y
  where
   open module Pp = Point p

-- The final difference between records and datatypes is that we have
-- η-equality on records.

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

η-Point : (p : Point) -> p == record { x = Point.x p; y = Point.y p }
η-Point p = refl

{-

  The empty record

-}

-- One interesting benefit of this is that we get a unit type with
-- η-equality.
record True : Set where

tt : True
tt = record{}

-- Now, since any element of True is equal to tt, metavariables of
-- type True will simply disappear. The following cute example exploits
-- this:

data False : Set where

NonZero : Nat -> Set
NonZero zero    = False
NonZero (suc _) = True

-- We make the proof that m is non-zero implicit.

_/_ : (n m : Nat){p : NonZero m} -> Nat
(n / zero) {}
zero  / suc m = zero
suc n / suc m = div (suc n) (suc m) m
  where
    div : Nat -> Nat -> Nat -> Nat
    div  zero    zero   c = suc zero
    div  zero   (suc y) c = zero
    div (suc x)  zero   c = suc (div x c c)
    div (suc x) (suc y) c = div x y c

-- Now, as long as we're dividing by things which are obviously
-- NonZero we can completely ignore the proof.

five = 17 / 3

{-

  A dependent record

-}

-- Of course, records can be dependent, and have parameters.
record ∃ {A : Set}(P : A -> Set) : Set where
  field
    witness : A
    proof   : P witness
