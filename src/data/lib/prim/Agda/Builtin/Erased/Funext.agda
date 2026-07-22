------------------------------------------------------------------------
-- Postulated, erased function extensionality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --erased-funext #-}

module Agda.Builtin.Erased.Funext where

open import Agda.Builtin.Equality

private variable
  A   : Set _
  P   : A → Set _
  f g : (x : A) → P x

-- Function extensionality.
--
-- This statement is not of the form "certain functions are
-- equivalences", but it is logically equivalent to such a statement,
-- and it does not depend on a definition of equivalence.

postulate
  @0 funext : (∀ x → f x ≡ g x) → f ≡ g
