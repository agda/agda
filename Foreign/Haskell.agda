------------------------------------------------------------------------
-- Types used (only) when calling out to Haskell via the FFI
------------------------------------------------------------------------

module Foreign.Haskell where

import Data.Colist as C; open C using ([]; _∷_)

------------------------------------------------------------------------
-- Simple types

-- A unit type.

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}
