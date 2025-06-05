module Test1 where

open import Nat1

-- Use the imported rewrite rule
test : (n : Nat) → n + 0 ≡ n
test n = refl
