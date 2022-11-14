-- Andreas, 2022-10-11, issue #6168
-- Don't crash if BUILTIN LEVELZERO is missing, give a proper error.

{-# OPTIONS --no-load-primitives #-}

{-# BUILTIN TYPE Type #-}
{-# BUILTIN PROP Prop #-}
{-# BUILTIN SETOMEGA Typeω #-}
{-# BUILTIN STRICTSET SSet #-}
{-# BUILTIN STRICTSETOMEGA SSetω #-}

postulate
  Level : Type

{-# BUILTIN LEVEL Level #-}

postulate IO : ∀ {a} → Type a → Type a

-- Expected Error:

-- No binding for builtin thing LEVELZERO, use {-# BUILTIN LEVEL name #-}
-- to bind it to 'name'
-- when checking that the expression Type a is a type
