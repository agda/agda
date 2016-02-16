open import Common.Prelude
open import Common.Reflection

module TermSplicing1 where

x = unquote (give Set)
