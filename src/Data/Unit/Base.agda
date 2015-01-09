------------------------------------------------------------------------
-- The Agda standard library
--
-- The unit type and the total relation on unit
------------------------------------------------------------------------
module Data.Unit.Base where

------------------------------------------------------------------------
-- A unit type defined as a record type

-- Note that the name of this type is "\top", not T.

record ⊤ : Set where
  constructor tt

record _≤_ (x y : ⊤) : Set where
