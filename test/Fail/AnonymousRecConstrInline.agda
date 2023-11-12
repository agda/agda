module AnonymousRecConstrInline where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

-- Tests that constructor → copattern inlining works even if the
-- constructor is not named.

record R : Set₁ where
  no-eta-equality
  field
    x : Set

{-# INLINE R.constructor #-}

t1 t2 : R
t1 = record { x = Nat }
t2 = record { x = Nat }

_ : t1 ≡ t2
_ = refl
