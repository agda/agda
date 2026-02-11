{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

foo : (x : Nat) (@rew p : 0 ≡ x) → Nat
foo = λ x (@rew p : 0 ≡ x) → 0

postulate D : Nat → Set

bar = λ (x : Nat) (@rew p : 0 ≡ x) (a : D x) (b : D 0) (q : a ≡ b) → 0
