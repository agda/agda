{-# OPTIONS --universe-polymorphism #-}
module tests.Literals where

open import Prelude.Nat
open import Prelude.Float
open import Prelude.Char
open import Prelude.String
open import Prelude.Unit
open import Prelude.IO

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
