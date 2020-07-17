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
  max-diag-s : max (suc m) (suc m) ≡ suc m -- for global confluence
  max-assoc : max (max k l) m ≡ max k (max l m)

{-# REWRITE max-0l max-0r #-}
{-# REWRITE max-ss max-diag max-diag-s #-}
--{-# REWRITE max-assoc #-} -- not confluent!

postulate
  _+_ : Nat → Nat → Nat
  plus-0l : 0 + n ≡ n
  plus-0r : m + 0 ≡ m
  plus-00 : 0 + 0 ≡ 0  -- for global confluence
  plus-suc-l : (suc m) + n ≡ suc (m + n)
  plus-suc-0 : (suc m) + 0 ≡ suc m -- for global confluence
  plus-suc-r : m + (suc n) ≡ suc (m + n)
  plus-0-suc : 0 + (suc n) ≡ suc n
  plus-suc-suc : (suc m) + (suc n) ≡ suc (suc (m + n))
  plus-assoc : (k + l) + m ≡ k + (l + m) -- not accepted by global confluence check

{-# REWRITE plus-00 plus-0l plus-0r
            plus-suc-l plus-suc-0
            plus-suc-r plus-0-suc
            plus-suc-suc #-}

postulate
  _*_ : Nat → Nat → Nat
  mult-0l : 0 * n ≡ 0
  mult-0r : m * 0 ≡ 0
  mult-00 : 0 * 0 ≡ 0
  mult-suc-l : (suc m) * n ≡ n + (m * n)
  mult-suc-l-0 : (suc m) * 0 ≡ 0
  mult-suc-r : m * (suc n) ≡ (m * n) + m
  plus-mult-distr-l : k * (l + m) ≡ (k * l) + (k * m)
  plus-mult-distr-r : (k + l) * m ≡ (k * m) + (l * m)
  mult-assoc : (k * l) * m ≡ k * (l * m)

{-# REWRITE mult-0l mult-0r mult-00
            mult-suc-l mult-suc-l-0 #-}
--{-# REWRITE mult-suc-r #-} -- requires rule plus-assoc!
--{-# REWRITE plus-mult-distr-l #-}
--{-# REWRITE plus-mult-distr-r #-}
--{-# REWRITE mult-assoc #-}
