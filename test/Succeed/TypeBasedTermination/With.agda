-- Tests with-function
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.With where

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

mapMaybe : {A B : Set} → (A → Maybe B) → List A → List B
mapMaybe p nil      = nil
mapMaybe p (cons x xs) with p x
... | just y  = cons y (mapMaybe p xs)
... | nothing = mapMaybe p xs
