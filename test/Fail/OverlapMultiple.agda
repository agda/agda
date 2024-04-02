module OverlapMultiple where

postulate
  X : Set
  instance x : X

{-# OVERLAPPING x #-}
{-# INCOHERENT x #-}
