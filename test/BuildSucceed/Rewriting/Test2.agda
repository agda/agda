module Test2 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
import Nat2

-- Use the imported rewrite rule
test : (n : Nat) → n + 0 ≡ n
test n = refl
