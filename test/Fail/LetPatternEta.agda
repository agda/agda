module LetPatternEta where

open import Agda.Builtin.Equality

record Wrap (A : Set) : Set where
  constructor wrap; no-eta-equality; pattern
  field unwrap : A
open Wrap

fails : ∀ {A} → Wrap A → Set
fails = \(wrap a) → a

-- fails : ∀ {A} → Wrap A → Set
-- fails w = let wrap a = w in _
