{-# OPTIONS --safe --erased-cubical #-}

module Erased-cubical where

-- Modules that use --cubical can be imported.

open import Erased-cubical.Cubical-again

-- Code from such modules that was originally defined in modules using
-- --without-K or --erased-cubical can be used without restrictions.

_ : {A : Set} → A → ∥ A ∥ᴱ
_ = ∣_∣

_ : D
_ = c

-- Matching on an erased constructor that was defined in a module that
-- uses --cubical is fine, and makes it possible to use erased
-- definitions in the right-hand side.

f : D′ → D′
f c′ = c′
