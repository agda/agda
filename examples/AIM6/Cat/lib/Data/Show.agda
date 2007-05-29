
module Data.Show where

import Prelude
import Data.Nat
import Data.Integer
import Data.String
import Data.List

open Prelude
open Data.Nat
open Data.Integer using (Int; pos; neg)
open Data.String
open Data.List hiding (_++_)

showNat : Nat -> String
showNat zero = "0"
showNat n    = fromList $ reverse $ toList $ show n
  where
    digit : Nat -> String
    digit 0 = "0"
    digit 1 = "1"
    digit 2 = "2"
    digit 3 = "3"
    digit 4 = "4"
    digit 5 = "5"
    digit 6 = "6"
    digit 7 = "7"
    digit 8 = "8"
    digit 9 = "9"
    digit _ = "?"

    show : Nat -> String
    show zero = ""
    show n    = digit (mod n 10) ++ show (div n 10)

showInt : Int -> String
showInt (pos n) = showNat n
showInt (neg n) = "-" ++ showNat (suc n)

