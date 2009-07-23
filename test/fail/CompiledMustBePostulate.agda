-- Compiled things must be a postulate

module CompiledMustBePostulate where

postulate
  A : Set

foo : Set
foo = A

{-# COMPILED foo bar #-}
