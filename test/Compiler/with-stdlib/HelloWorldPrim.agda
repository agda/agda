module HelloWorldPrim where

open import IO.Primitive
open import Data.String

main = putStrLn (toCostring "Hello World!")
