{-# OPTIONS --polarity #-}

module _ where

module M (@- A : Set₁) where
  @- B : Set₁
  B = A → Set
