-- Andreas, 2025-11-18, issue #7664
-- Exploiting a bug in checkParameters leading Agda to skip some constructor parameters.

module Issue7664a where

open import Agda.Builtin.String
open import Agda.Builtin.Equality

typeOf : {A : Set} (a : A) → Set
typeOf {A} a = A

record ⊤ : Set where

data Access : Set where
  pub priv : Access

Key : Access → Set
Key pub  = ⊤
Key priv = String

-- This module defines a data type `Secret` and an inhabitant `key`
-- which should be opaque since the constructor of `Secret`
-- is not exported.
-- However, due to issue #7664 one can match on `Secret`
-- using the constructor `peek` of a different type, `Public`.

module Definitions where

  private
    module Private (a : Access) where
      data Wrap : Set where
        wrap : Key a → Wrap

  module M (D : Set) where
    open Private pub  public renaming (Wrap to Public; wrap to peek)
    open Private priv public using () renaming (Wrap to Secret)

    key : Secret
    key = Private.wrap "My secret key"

  open M public

open Definitions using (Public; peek; Secret; key)

-- This definition should be rejected.
look : Secret ⊤ → String
look (peek secret) = secret

-- Expected error: [UnequalTerms]
-- The terms
--   pub
-- and
--   priv
-- are not equal at type Access
-- when checking that the pattern peek secret has type Secret ⊤

-- WAS: The secret is leaked.
leak : String
leak = look (key ⊤)
