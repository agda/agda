module Prelude.Exit where

open import Prelude.Char
open import Prelude.IO
open import Prelude.Unit

postulate
  exit : Char → IO Unit

{-# COMPILED_EPIC exit (n : Int, u : Unit) ->
                       Unit = foreign Unit "exit" (n : Int) #-}

exitSuccess : Char
exitSuccess = '\NUL'

exitFailure : Char
exitFailure = '\SOH'
