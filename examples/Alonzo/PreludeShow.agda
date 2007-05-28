
module PreludeShow where
import RTP -- magic module

import AlonzoPrelude as Prelude
open import PreludeNat
open import PreludeString
import PreludeList
open import PreludeBool

open Prelude
-- open Data.Integer, using (Int, pos, neg)
open PreludeList hiding (_++_)


showInt : Int -> String
showInt = RTP.primShowInt

showNat : Nat -> String
showNat n = showInt (RTP.primNatToInt n)

{-
showNat : Nat -> String
showNat zero = "0"
showNat n    =  reverseString $ show n
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
-}

{-
showInt : Int -> String
showInt (pos n) = showNat n
showInt (neg n) = "-" ++ showNat (suc n)
-}

showChar : Char -> String
showChar = RTP.primShowChar

showBool : Bool -> String
showBool true = "true"
showBool false = "false"

primitive
  primShowFloat : Float -> String

showFloat : Float -> String
showFloat = primShowFloat