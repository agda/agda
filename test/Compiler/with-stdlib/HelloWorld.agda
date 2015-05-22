module HelloWorld where

open import IO
open import Data.String
open import Data.Unit

main = run (putStrLn "Hello World!")
