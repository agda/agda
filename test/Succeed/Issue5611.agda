{-# OPTIONS --without-K --safe #-}

data D : Set where
  c : D → D

variable
  x y : D

data P : D → D → Set where
  c : P (c x) (c y)

record Q (y : D) : Set where

G : .(Q y) → P x y → Set₁
G _ c = Set
