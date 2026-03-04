open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

-- Variant of #165
module Issue8443b where

postulate X : Set

module R₀ (X : Set) where
  postulate P : Set

module R₁ (X : Set) where
  open R₀ X public

open R₁ X
postulate p : P
