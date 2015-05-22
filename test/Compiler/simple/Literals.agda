{-# OPTIONS --universe-polymorphism #-}
module Literals where

open import Common.Nat
open import Common.Float
open import Common.Char
open import Common.String
open import Common.Unit
open import Common.IO

afloat : Float
afloat = 1.23

astring : String
astring = "abc"

achar : Char
achar = 'd'

anat : Nat
anat = 123

main : IO Unit
main =
  printFloat  afloat  ,,
  putStr      astring ,,
  printChar   achar   ,,
  printNat    anat    ,,
  putStrLn ""
