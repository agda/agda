{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data Unit : Set where ∗ : Unit

postulate
  A : Set
  a b c : Unit → A
  a→b : a ∗ ≡ b ∗
  a→c : ∀ x → a x ≡ c x
  a→c' : a ∗ ≡ c ∗      -- for global confluence checker
  b→c : b ∗ ≡ c ∗

{-# REWRITE a→b a→c a→c' b→c #-}
