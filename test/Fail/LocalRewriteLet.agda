{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module _ where

bar : (x : Nat) → 0 ≡ x → Nat
bar x p = let @rew q : 0 ≡ x
              q = p
           in x
