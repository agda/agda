{-# OPTIONS --rewriting --local-confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

postulate
  +-ass : ∀ {n m l} → (n + m) + l ≡ n + (m + l)

{-# REWRITE +-ass #-}
