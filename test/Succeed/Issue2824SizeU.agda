-- Andreas, 2017-11-01, issue #2824
-- Allow built-ins that define a new name to be in parametrized module.

{-# OPTIONS --sized-types #-}

module Issue2824SizeU (A : Set) where  -- This is the top-level module header.

{-# BUILTIN SIZEUNIV SizeU #-}

-- Should succeed.
