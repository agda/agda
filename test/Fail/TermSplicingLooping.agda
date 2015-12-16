open import Common.Prelude
open import Common.Reflection
open import Common.TC

module TermSplicingLooping where

mutual
  f : Set -> Set
  f = unquote (give (def (quote f) []))
