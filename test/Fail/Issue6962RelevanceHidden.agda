module Issue6962RelevanceHidden where

open import Agda.Builtin.Nat

bad .{@irrelevant n : Nat} : Nat
bad = zero
