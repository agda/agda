open import Common.Prelude
open import Common.Reflection
open import Common.TC

module TermSplicingOutOfScope where

f : Set → Set → Set → Set
f x y z = unquote (give (var 3 []))
