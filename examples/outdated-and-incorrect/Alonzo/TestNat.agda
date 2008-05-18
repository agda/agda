module TestNat where
import PreludeNatType
import AlonzoPrelude
import PreludeNat
import PreludeString
import PreludeShow
import RTP
import PreludeList

open AlonzoPrelude
open PreludeShow
open PreludeNatType
open PreludeString
open PreludeNat
open PreludeList hiding(_++_)
one = suc zero
two = suc one

lines : (List String) -> String
lines [] = ""
lines (l :: []) = l
lines (l :: ls) = l ++ "\n" ++ (lines ls)

mainS = (id ○ lines) ((showNat 42) :: (showBool (2007 == 2007)) :: [])
