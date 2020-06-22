{-# OPTIONS --rewriting --allow-unsolved-metas #-}

postulate _↦_ : Set → Set → Set
{-# BUILTIN REWRITE _↦_ #-}

postulate
  X : Set
  P : Set → Set → Set
  P-rewr : (A : Set) → (P A A ↦ X)
  {-# REWRITE P-rewr #-}

f : (B : Set → Set) {x y : Set} → P (B x) (B y)
f = {!!}
