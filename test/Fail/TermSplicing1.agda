open import Common.Prelude
open import Common.Reflection
open import Common.TC

module TermSplicing1 where

x = unquote (give Set)
