module CompileDefined where

open import Agda.Builtin.Nat

foo : Nat → Nat
foo x = x + x

-- Adding COMPILE to a defined function will trigger a warning,
-- since the COMPILE pragma replaces the Agda definition in the
-- GHC backend, which could lead to unexpected behaviour.
{-# COMPILE GHC foo = \ x -> 2 #-}

-- No warning for abstract functions.
abstract
  bar : Nat → Nat
  bar x = x

{-# COMPILE GHC bar = \ x -> x #-}

-- No warning for INLINE functions: they only get UselessInline.
baz : Nat → Nat
baz x = x

{-# INLINE baz #-}
{-# COMPILE GHC baz = \ x -> x #-}

-- No warning for postulates: COMPILE is how they get a definition.
postulate
  qux : Nat → Nat

{-# COMPILE GHC qux = \ x -> x #-}
