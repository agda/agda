
module Common.Prelude where

{-# IMPORT Common.FFI #-}

import Common.Level
open import Common.Char public
open import Common.String public
open import Common.Bool public
open import Common.Nat public
open import Common.List public
open import Common.Unit public
open import Common.Nat public
open import Common.Float public
open import Common.IO public

data   ⊥ : Set where
record ⊤ : Set where

{-# BUILTIN UNIT ⊤ #-}
