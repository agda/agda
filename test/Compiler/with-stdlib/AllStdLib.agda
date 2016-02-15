module AllStdLib where

-- Ensure that the entire standard library is compiled.
import README

open import Data.Unit.Base
open import Data.String
open import IO
import IO.Primitive as Prim

main : Prim.IO ⊤
main = run (putStrLn "Hello World!")
