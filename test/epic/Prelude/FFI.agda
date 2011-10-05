{-# OPTIONS --includeC=helloworld.c #-}
module Prelude.FFI where

open import Prelude.IO
open import Prelude.String
open import Prelude.Unit

postulate
  helloworld : IO Unit
  test : IO String
  
{-# COMPILED_EPIC helloworld (u : Unit) -> Unit = foreign Unit "hello_world" () #-}
{-# COMPILED_EPIC test (u : Unit) -> Unit = foreign String "test" () #-}

main : IO Unit
main = 
  helloworld ,,
  x <- test ,
  putStrLn x