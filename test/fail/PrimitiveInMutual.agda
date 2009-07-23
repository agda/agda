
-- Currently primitive functions are not allowed in mutual blocks.
-- This might change.
module PrimitiveInMutual where

postulate String : Set
{-# BUILTIN STRING String #-}

mutual
  primitive primStringAppend : String -> String -> String

  _++_ : String -> String -> String
  x ++ y = primStringAppend x y

