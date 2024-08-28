{-# OPTIONS --guardedness #-}

module TrustMe where

open import Data.String
open import Data.String.Unsafe
open import Data.Unit.Polymorphic using (⊤)
open import IO
import IO.Primitive.Core as Prim
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Level using (0ℓ)

-- Check that trustMe works.

testTrustMe : IO {0ℓ} ⊤
testTrustMe with "apa" ≟ "apa"
... | yes refl = putStrLn "Yes!"
... | no  _    = putStrLn "No."

main : Prim.IO ⊤
main = run testTrustMe
