------------------------------------------------------------------------
-- The Agda standard library
--
-- Type(s) used (only) when calling out to Haskell via the FFI
------------------------------------------------------------------------

module Foreign.Haskell where

-- A unit type.

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}
