module TrustMe where

open import Data.String
open import Data.Unit using (⊤)
open import IO
import IO.Primitive as Prim
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Check that trustMe works.

testTrustMe : IO ⊤
testTrustMe with "apa" ≟ "apa"
... | yes refl = putStrLn "Yes!"
... | no  _    = putStrLn "No."

main : Prim.IO ⊤
main = run testTrustMe
