module Issue1691 where

open import Common.Equality
open import Issue1691.Nat  -- works if we inline this module

∸1≗pred :  ∀ n → n ∸ suc 0 ≡ pred n  -- works if zero is replaced by 0
∸1≗pred zero    = refl
∸1≗pred (suc _) = refl
