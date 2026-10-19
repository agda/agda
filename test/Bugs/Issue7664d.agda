
-- Andreas, 2026-09-25, issue #7664.
--
-- Known limitation of the parameter check in `checkParameters`:
-- a module instantiation may constrain the parameters of the original
-- without fixing any of them to a closed term, by passing one of its own
-- parameters twice.  The check neutralizes all positions that mention the
-- parameters of the copy, so it does not notice that `Diag.D Y` can only
-- ever be `Private.Wrap Y Y`.
--
-- Thus, the following leak survives, in the same spirit as Issue7664a.agda.
-- Should be rejected, but is currently accepted.

{-# OPTIONS --safe #-}

-- {-# OPTIONS -v tc.lhs.split:40 #-}

module Issue7664d where

open import Agda.Builtin.String
open import Agda.Builtin.Equality

record ⊤ : Set where
  constructor tt

module Definitions where

  private
    module Private (a : Set) (b : Set) where
      data Wrap : Set where
        wrap : a → b → Wrap

  -- Exported: only the *diagonal* copy, Diag.D Y = Private.Wrap Y Y.
  module Diag (Y : Set) where
    open module PD = Private Y Y public renaming (Wrap to D; wrap to mk)

  -- Exported: an off-diagonal type (without its constructor) and an inhabitant.
  open module PTS = Private ⊤ String public using () renaming (Wrap to Sec)

  key : Sec
  key = Private.wrap tt "My secret key"

open Definitions using (module Diag; Sec; key)

-- Should be rejected: Diag.mk only ever constructs `Private.Wrap Y Y`.
look : Sec → String
look (Diag.mk x y) = y

-- The secret is leaked.
leak : String
leak = look key

_ : leak ≡ "My secret key"
_ = refl
