{-# OPTIONS --rewriting --confluence-check #-}


open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  k l m n : Nat

postulate
  max : Nat → Nat → Nat
  max-0l : max 0 n ≡ n
  max-0r : max m 0 ≡ m
  max-diag : max m m ≡ m
  max-ss : max (suc m) (suc n) ≡ suc (max m n)
  max-assoc : max (max k l) m ≡ max k (max l m)

{-# REWRITE max-0l #-}
{-# REWRITE max-0r #-}
{-# REWRITE max-diag #-}
{-# REWRITE max-ss #-}
{-# REWRITE max-assoc #-} -- not confluent!
