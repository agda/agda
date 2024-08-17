module OpaqueUnfolding where

open import Agda.Builtin.Nat

opaque
  foo : Set₁
  foo = Set

opaque
  unfolding foo
  -- Unfolds bar
  bar : foo
  bar = Nat

opaque
  unfolding bar
  -- Unfolds foo and bar
  ty : Set
  ty = bar

  quux : ty
  quux = zero

-- Andreas, 2024-08-17
-- Trigger scope checker warnings

module _ (A : Set) where

  opaque            -- UselessOpaque
    unfolding Set   -- UnfoldTransparentName
    unfolding A     -- UnfoldingWrongName
    unfolding B     -- NotInScope
    unfolding Set1
