-- Andreas, 2022-10-06, issue #6168
-- Don't crash if BUILTIN LEVEL is missing, give a proper error.

{-# OPTIONS --no-load-primitives #-}

{-# BUILTIN TYPE Type #-}
{-# BUILTIN PROP Prop #-}
{-# BUILTIN SETOMEGA Typeω #-}
{-# BUILTIN STRICTSET SSet #-}
{-# BUILTIN STRICTSETOMEGA SSetω #-}

postulate IO : ∀ {a} → Type a → Type a

-- Expected Error:

-- No binding for builtin thing LEVEL, use {-# BUILTIN LEVEL name #-}
-- to bind it to 'name'
-- when checking that the expression Type a is a type
