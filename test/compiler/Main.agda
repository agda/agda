module Main where

-- Ensure that the entire library is compiled.
import README

open import Coinduction
open import Data.String
open import Data.Unit using (⊤)
open import IO
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Check that trustMe works.

testTrustMe : IO ⊤
testTrustMe with "apa" ≟ "apa"
... | yes refl = putStrLn "Yes!"
... | no  _    = putStrLn "No."

-- Check that ∞ can be used as an "expression".

testInf : Set → Set
testInf = ∞

main = run testTrustMe
