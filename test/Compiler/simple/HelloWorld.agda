module HelloWorld where

open import Common.IO
open import Common.Unit

main : IO Unit
main = putStr "Hello World"
