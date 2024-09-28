module _ where

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

-- Not allowed:
{-# COMPILE GHC Bool = data Bool (True | False) #-}

-- Error when compiling:

-- Conflicting GHC pragmas for Bool at
--   - test/Fail/CompiledBuiltinBool.agda:6.1-26
--   - test/Fail/CompiledBuiltinBool.agda:11.1-52
