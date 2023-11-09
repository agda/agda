module AnonymousRecConstrInline where

-- Tests that you can mark the constructor of a no-eta-equality record
-- as INLINE even if the constructor is not named.

open import Agda.Builtin.Nat

record R : Set₁ where
  no-eta-equality
  field
    x : Set

{-# INLINE R.constructor #-}
