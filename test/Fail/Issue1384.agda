-- {-# OPTIONS --no-coverage #-}
-- {-# OPTIONS -v tc.cover:20 #-}

open import Common.Bool
open import Common.Equality

_∨_ : Bool → Bool → Bool
a ∨ b = if a then true else b

module Works where
  data Term : Bool → Set where
    I   : Term false
    App : ∀ a b c → a ∨ b ≡ c → Term a → Term b → Term c

  -- The following clause works for the coverage checker:

  test : Term false → Set
  test (App false false .false refl I x) = Bool

module Fails where

  data Term : Bool -> Set where
    I   : Term false
    App : ∀ a b c → Term a → Term b → a ∨ b ≡ c → Term c

  -- If we put the equality proof later in App, it fails:

  test : Term false → Set
  test (App false false .false I x refl) = Bool
  -- The following checks, until you split at p.
  -- test (App false false .false I x p) = {!p!}
