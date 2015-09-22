-- Compiled things must have a Haskell type given by a COMPILED_TYPE pragma

module CompiledMustHaveHaskellType where

postulate
  N : Set
  foo : N

-- It is necessary add something like
-- {-# COMPILED_TYPE N Int #-}

{-# COMPILED foo bar #-}
