{-# OPTIONS --cumulativity #-}

postulate
  F : (X : Set) → X → Set
  X : Set₁
  a : X
  shouldfail : F _ a
