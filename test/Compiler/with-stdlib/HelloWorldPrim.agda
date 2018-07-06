module HelloWorldPrim where

open import IO.Primitive
open import Codata.Musical.Costring

main = putStrLn (toCostring "Hello World!")
