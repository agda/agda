{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable
  k l m n : Nat

postulate
  _+_ : Nat → Nat → Nat
  plus-0l : 0 + n ≡ n
  plus-0r : m + 0 ≡ m
  plus-suc-l : (suc m) + n ≡ suc (m + n)
  plus-suc-r : m + (suc n) ≡ suc (m + n)
  plus-assoc : (k + l) + m ≡ k + (l + m)

{-# REWRITE plus-0l #-}
{-# REWRITE plus-0r #-}
{-# REWRITE plus-suc-l #-}
{-# REWRITE plus-suc-r #-}
{-# REWRITE plus-assoc #-}

postulate
  _*_ : Nat → Nat → Nat
  mult-0l : 0 * n ≡ 0
  mult-0r : m * 0 ≡ 0
  mult-suc-l : (suc m) * n ≡ n + (m * n)
  mult-suc-r : m * (suc n) ≡ (m * n) + m
  plus-mult-distr-l : k * (l + m) ≡ (k * l) + (k * m)
  plus-mult-distr-r : (k + l) * m ≡ (k * m) + (l * m)
  mult-assoc : (k * l) * m ≡ k * (l * m)

{-# REWRITE mult-0l #-}
{-# REWRITE mult-0r #-}
{-# REWRITE mult-suc-l #-}
{-# REWRITE mult-suc-r #-} -- requires rule plus-assoc!
{-# REWRITE plus-mult-distr-l #-}
