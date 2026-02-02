{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- For now, this is not allowed, but it eventually should be
foo : (x : Nat) → @rew x ≡ 0 → Nat
foo x p = 0
