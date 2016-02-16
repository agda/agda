open import Common.Prelude
open import Common.Reflection

module TermSplicingOutOfScope where

f : Set → Set → Set → Set
f x y z = unquote (give (var 3 []))
