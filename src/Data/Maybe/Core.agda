------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Maybe.

module Data.Maybe.Core where

open import Level

data Maybe {a} (A : Set a) : Set a where
  just    : (x : A) → Maybe A
  nothing : Maybe A

{-# IMPORT Data.FFI #-}
{-# COMPILED_DATA Maybe Data.FFI.AgdaMaybe Just Nothing #-}
