
module _ (A : Set) where

open import Common.Prelude
open import Common.Reflection
open import Common.TC

macro
  foo : Tactic
  foo _ = returnTC _

bar : ⊤
bar = foo
