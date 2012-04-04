
module Issue561 where

open import Common.Char
open import Common.Prelude

primitive
  primIsDigit : Char → Bool

postulate
  IO : Set → Set
  return : ∀ {A} → A → IO A

{-# BUILTIN IO IO #-}

main : IO Bool
main = return true