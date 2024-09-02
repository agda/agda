module WarningOnUsage where

id : {A : Set} → A → A
id x = x

-- Deprecated names

λx→x = id

{-# WARNING_ON_USAGE λx→x "DEPRECATED: Use `id` instead of `λx→x`" #-}

open import Agda.Builtin.Equality

_ : {A : Set} {x : A} → λx→x x ≡ x
_ = refl

module _ (A : Set) where

  -- Andreas, 2024-08-16
  -- Dead pragmas because of scope errors:

  {-# WARNING_ON_USAGE A "Not a defined name: A" #-}
  {-# WARNING_ON_USAGE x "Not in scope: x"       #-}
