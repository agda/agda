module tests.HelloWorld where

open import Prelude.IO
open import Prelude.Unit

main : IO Unit
main = putStr "Hello World"
