{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data Unit : Set where ∗ : Unit

postulate
  A : Set
  a b c : Unit → A
  a→b : a ∗ ≡ b ∗
  a→c : ∀ x → a x ≡ c x
  b→c : b ∗ ≡ c ∗

{-# REWRITE a→b a→c b→c #-}
