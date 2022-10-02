{-# OPTIONS --type-in-type --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  id : Set → Set
  rew-id : (A : Set) → id A ≡ A
{-# REWRITE rew-id #-}

postulate
  F : Set → Set

postulate
  f : Set → Set
  g : Set → Set → Set
  rew-fg : (A : Set) → g A (f A) ≡ Set
{-# REWRITE rew-fg #-}

test : (δ : Set) → g (F δ) (f (F (id δ)))
test _ _ = {!!}
