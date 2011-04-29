open import Common.Prelude
open import Common.Reflect

module TermSplicingOutOfScope where

f : Set → Set → Set → Set
f x y z = unquote (var 3 [])
