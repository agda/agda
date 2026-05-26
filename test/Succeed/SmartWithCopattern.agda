{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat renaming (zero to ze; suc to su)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

foo : (n : Nat) → Σ Nat (_≡ n + n)
foo n .fst with n + n
... | ze   = ze
... | su m = su m
foo n .snd with n + n
... | ze   = refl
... | su m = refl
