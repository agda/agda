{-# OPTIONS --type-in-type --rewriting --allow-unsolved-metas #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  F : Set → Set → Set
  G : (Set → Set) → Set → Set → Set
  rewF : (A : Set) → F A A ≡ Set
  rewG : (A : Set → Set) (X Y : Set) → G A X Y ≡ F (A X) (A Y)
{-# REWRITE rewF rewG #-}

test : (A : Set → Set) → G A _ _
test A x = {!!}
