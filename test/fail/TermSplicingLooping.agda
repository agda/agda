open import Common.Prelude
open import Common.Reflect

module TermSplicingLooping where

mutual
  f : Set -> Set
  f = unquote (def (quote f) [])
