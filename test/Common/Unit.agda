module Common.Unit where

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}
{-# COMPILED_DATA_UHC Unit __UNIT__ __UNIT__ #-}
