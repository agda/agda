------------------------------------------------------------------------
-- Strings
------------------------------------------------------------------------

module Prelude.String where

------------------------------------------------------------------------
-- The type

postulate String : Set

{-# BUILTIN STRING String #-}

private
  primitive primStringAppend : String -> String -> String

_++_ : String -> String -> String
_++_ = primStringAppend
