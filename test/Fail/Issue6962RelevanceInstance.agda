module Issue6962RelevanceInstance where

open import Agda.Builtin.Nat

bad .{{@irrelevant n : Nat}} : Nat
bad = zero
