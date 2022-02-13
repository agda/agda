{-# OPTIONS --safe --cubical #-}

module Erased-cubical.Cubical-again where

open import Agda.Builtin.Cubical.Path

open import Erased-cubical.Erased public

-- Code defined using --erased-cubical can be imported and used by
-- regular Cubical Agda code.

_ : {A : Set} → A → ∥ A ∥ᴱ
_ = ∣_∣

-- The constructor trivialᶜ is defined in a module that uses --cubical
-- and re-exported from a module that uses --erased-cubical. Because
-- the current module uses --cubical it is fine to use trivialᶜ in a
-- non-erased setting.

_ : {A : Set} (x y : ∥ A ∥ᶜ) → x ≡ y
_ = trivialᶜ
