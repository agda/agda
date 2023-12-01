{-# OPTIONS --rewriting --guardedness --sized-types #-}

module AllStdLib where

-- Ensure that the entire standard library is compiled.
import Everything

open import Data.Unit.Polymorphic using (⊤)
open import Data.String
open import IO using (putStrLn; run)
open import IO.Primitive using (IO; _>>=_)

import DivMod
import HelloWorld
import HelloWorldPrim
import ShowNat
import TrustMe
import Vec
import dimensions

infixr 1 _>>_
_>>_ : ∀ {A B : Set} → IO A → IO B → IO B
m >> m₁ = m >>= λ _ → m₁

main : IO ⊤
main = do
  run (putStrLn "Hello World!")
  DivMod.main
  HelloWorld.main
  HelloWorldPrim.main
  ShowNat.main
  TrustMe.main
  Vec.main
  dimensions.main
