module TelescopePatternEta where

open import Agda.Builtin.Equality

record Wrap (A : Set) : Set where
  constructor wrap; no-eta-equality; pattern
  field unwrap : A
open Wrap

module _ {A} (w@(wrap a) : Wrap A) where
