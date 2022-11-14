{-# OPTIONS --type-in-type --rewriting --allow-unsolved-metas #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  Id : (Set → Set) → Set → Set → Set
  ext : Set → Set → Set
  refl↓ : (A : Set) → ext A A ≡ Set
  Id-∙ : (A : Set → Set) (X Y : Set) → Id A X Y ≡ ext (A X) (A Y)
{-# REWRITE refl↓ Id-∙ #-}

frob-ap-kan : (A : Set → Set) → Set ≡ Set → Id A _ _
frob-ap-kan A refl = {!!}
