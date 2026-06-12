------------------------------------------------------------------------
-- Postulated, erased propositional extensionality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --propext #-}

module Agda.Builtin.Propext where

open import Agda.Builtin.Equality
open import Agda.Primitive

private variable
  a   : Level
  A B : Set _

-- The property of being a proposition.

Is-proposition : Set a → Set a
Is-proposition A = (x y : A) → x ≡ y

-- Propositional extensionality.

postulate
  @0 propext :
       Is-proposition A → Is-proposition B →
       (A → B) → (B → A) → A ≡ B
