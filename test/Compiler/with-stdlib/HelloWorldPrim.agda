{-# OPTIONS --guardedness #-}

module HelloWorldPrim where

open import IO.Primitive.Infinite
open import Codata.Musical.Costring

main = putStrLn (toCostring "Hello World!")
