-- Andreas, 2022-10-06, issue #6128
-- Make sure you can use BUILTIN TYPE already in the same file.

{-# OPTIONS --no-load-primitives #-}

{-# BUILTIN TYPE Type #-}
{-# BUILTIN PROP Prop #-}
{-# BUILTIN SETOMEGA Typeω #-}
{-# BUILTIN STRICTSET SSet #-}
{-# BUILTIN STRICTSETOMEGA SSetω #-}

record ⊤ : Type where

-- WAS: internal error because scope checker tried to use BUILTIN TYPE.
-- Should pass.
