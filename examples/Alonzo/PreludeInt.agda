module PreludeInt where
open import AlonzoPrelude
import RTP

int : Nat -> Int
int = RTP.primNatToInt

_+_ : Int -> Int -> Int
_+_ = RTP.primIntAdd


_-_ : Int -> Int -> Int
_-_ = RTP.primIntSub

_*_ : Int -> Int -> Int
_*_ = RTP.primIntMul

div : Int -> Int -> Int
div = RTP.primIntDiv

mod : Int -> Int -> Int
mod = RTP.primIntMod



