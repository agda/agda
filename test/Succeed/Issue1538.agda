
module _ (A : Set) where

open import Common.Prelude
open import Common.Reflection

macro
  foo : Tactic
  foo _ = returnTC _

bar : ⊤
bar = foo
