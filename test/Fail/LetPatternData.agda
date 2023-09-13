module LetPatternData where

open import Agda.Builtin.Equality

data Wrap (A : Set) : Set where
  wrap : A → Wrap A
open Wrap

fails : ∀ {A} → Wrap A → Set
fails w = let wrap a = w in _
