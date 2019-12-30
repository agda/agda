{-# OPTIONS --rewriting --confluence-check #-}
module Issue4333.M where

postulate
  A : Set
  _==_ : A → A → Set
{-# BUILTIN REWRITE _==_ #-}

postulate
  a a₀' a₁' : A
  p₀ : a == a₀'
  p₁ : a == a₁'
  B : A → Set
  b : B a

