
module AllStdLib where

-- Ensure that the entire standard library is compiled.
import README

open import Data.Unit.Polymorphic using (⊤)
open import Data.String
open import IO hiding (_>>_)
import IO.Primitive as Prim

import DivMod
import HelloWorld
import HelloWorldPrim
import ShowNat
import TrustMe
import Vec
import dimensions

infixr 1 _>>_
_>>_ : ∀ {A B : Set} → Prim.IO A → Prim.IO B → Prim.IO B
m >> m₁ = m Prim.>>= λ _ → m₁

main : Prim.IO ⊤
main = run (putStrLn "Hello World!") >>
       DivMod.main >>
       HelloWorld.main >>
       HelloWorldPrim.main >>
       ShowNat.main >>
       TrustMe.main >>
       Vec.main >>
       dimensions.main
