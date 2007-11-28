
module Data.Real.Base where

import Prelude
import Data.Rational
import Data.Nat as Nat
import Data.Bits
import Data.Bool
import Data.Maybe
import Data.Integer
import Data.List
import Data.Real.Gauge

open Prelude
open Data.Rational hiding (_-_; !_!)
open Data.Bits
open Data.Bool
open Data.List
open Data.Integer
       hiding   (-_; _+_; _≥_; _≤_; _>_; _<_; _==_)
       renaming ( _*_ to _*'_ )
open Nat using (Nat; zero; suc)
open Data.Real.Gauge using (Gauge)

Base  = Rational

bitLength : Int -> Int
bitLength x = pos (nofBits ! x !) - pos 1

approxBase : Base -> Gauge -> Base
approxBase x e = help err
  where
    num = numerator   e
    den = denominator e

    err = bitLength (den - pos 1) - bitLength num

    help : Int -> Base
    help (pos (suc n)) = round (x * fromNat k) % pos k
      where
        k = shiftL 1 (suc n)
    help (pos zero) = x
    help (neg n) = fromInt $ (round $ x / fromInt k) *' k
      where
        k = pos (shiftL 1 ! neg n !)

powers : Nat -> Base -> List Base
powers n x = iterate n (_*_ x) x

sumBase : List Base -> Base
sumBase xs = foldr _+_ (fromNat 0) xs

