{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module _ where

bar : (x : Nat) → @rew 0 ≡ x → Nat
bar x = λ p → x
