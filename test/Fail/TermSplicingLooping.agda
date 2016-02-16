open import Common.Prelude
open import Common.Reflection

module TermSplicingLooping where

mutual
  f : Set -> Set
  f = unquote (give (def (quote f) []))
