------------------------------------------------------------------------
-- The Maybe type
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Maybe.

module Data.Maybe.Core where

data Maybe (A : Set) : Set where
  just    : (x : A) → Maybe A
  nothing : Maybe A
