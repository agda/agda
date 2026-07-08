{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

foo : (x : Nat) → x ≡ suc x → Nat
foo x p rewrite p = refl
