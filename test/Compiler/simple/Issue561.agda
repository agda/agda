
module Issue561 where

open import Agda.Builtin.Bool
open import Issue561.Core

primitive
  primIsDigit : Char → Bool

main : IO Bool
main = return true
