{-# OPTIONS --no-termination-check #-}

module Data.Integer where

import Prelude
import Data.Nat as Nat
import Data.Bool

open Nat using (Nat; suc; zero)
         renaming ( _+_  to _+'_
                  ; _*_  to _*'_
                  ; _<_  to _<'_
                  ; _-_  to _-'_
                  ; _==_ to _=='_
                  ; div  to div'
                  ; mod  to mod'
                  ; gcd  to gcd'
                  ; lcm  to lcm'
                  )
open Data.Bool
open Prelude

data Int : Set where
  pos : Nat -> Int
  neg : Nat -> Int  -- neg n = -(n + 1)

infix 40 _==_ _<_ _>_ _≤_ _≥_
infixl 60 _+_ _-_
infixl 70 _*_
infix  90 -_

-_ : Int -> Int
- pos zero    = pos zero
- pos (suc n) = neg n
- neg n       = pos (suc n)

_+_ : Int -> Int -> Int
pos n + pos m = pos (n +' m)
neg n + neg m = neg (n +' m +' 1)
pos n + neg m =
  ! m <' n => pos (n -' m -' 1)
  ! otherwise neg (m -' n)
neg n + pos m = pos m + neg n

_-_ : Int -> Int -> Int
x - y = x + - y

!_! : Int -> Nat
! pos n ! = n
! neg n ! = suc n

_*_ : Int -> Int -> Int
pos 0 * _     = pos 0
_     * pos 0 = pos 0
pos n * pos m = pos (n *' m)
neg n * neg m = pos (suc n *' suc m)
pos n * neg m = neg (n *' suc m -' 1)
neg n * pos m = neg (suc n *' m -' 1)

div : Int -> Int -> Int
div _             (pos zero)    = pos 0
div (pos n)       (pos m)       = pos (div' n m)
div (neg n)       (neg m)       = pos (div' (suc n) (suc m))
div (pos zero)    (neg _)       = pos 0
div (pos (suc n)) (neg m)       = neg (div' n (suc m))
div (neg n)       (pos (suc m)) = div (pos (suc n)) (neg m)

mod : Int -> Int -> Int
mod _ (pos 0)       = pos 0
mod (pos n) (pos m) = pos (mod' n m)
mod (neg n) (pos m) = adjust (mod' (suc n) m)
  where
    adjust : Nat -> Int
    adjust 0 = pos 0
    adjust n = pos (m -' n)
mod n (neg m)       = adjust (mod n (pos (suc m)))
  where
    adjust : Int -> Int
    adjust (pos 0) = pos 0
    adjust (neg n) = neg n  -- impossible
    adjust x       = x + neg m

gcd : Int -> Int -> Int
gcd a b = pos (gcd' ! a ! ! b !)

lcm : Int -> Int -> Int
lcm a b = pos (lcm' ! a ! ! b !)

_==_ : Int -> Int -> Bool
pos n == pos m = n ==' m
neg n == neg m = n ==' m
pos _ == neg _ = false
neg _ == pos _ = false

_<_ : Int -> Int -> Bool
pos _ < neg _ = false
neg _ < pos _ = true
pos n < pos m = n <' m
neg n < neg m = m <' n

_≤_ : Int -> Int -> Bool
x ≤ y = x == y || x < y

_≥_ = flip _≤_
_>_ = flip _<_

