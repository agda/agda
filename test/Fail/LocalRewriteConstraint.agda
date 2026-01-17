{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- TODO: Fix the nonsense and vague error message
module _ where

foo : (x : Nat) → @rew 0 ≡ x → Nat
foo _ _ = 0

bar : (x : Nat) → 0 ≡ x → Nat
bar x p = foo x p
