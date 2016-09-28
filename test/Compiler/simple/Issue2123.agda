module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Common.IO
open import Common.Unit

data ⊥ : Set where

record Pair : Set where
  constructor _,_
  field fst snd : String

open Pair

record ERing : Set where
  constructor ering
  field divRem : (⊥ → ⊥) → Pair

open ERing

eRing : ERing
eRing = ering λ _ → "fst" , "snd"

test : String
test = snd (divRem eRing (λ ()))

main : IO Unit
main = putStrLn test
