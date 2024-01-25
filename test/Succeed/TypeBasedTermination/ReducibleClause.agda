-- Tests functions that are actually not recursive
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.ReducibleClause where

data B : Set where
 a1 a2 : B

data U : Set where
  unit : U

f : B → U
f a1 = f a2
f a2 = unit
