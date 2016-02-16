
module Issue561 where

open import Common.Prelude hiding (primIsDigit)

primitive
  primIsDigit : Char → Bool

main : IO Bool
main = return true
