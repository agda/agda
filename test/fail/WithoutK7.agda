{-# OPTIONS --without-K #-}

module WithoutK7 where

data I : Set where
  i : I

data D (x : I) : Set where
  d : D x

data P (x : I) : D x → Set where

Foo : ∀ x → P x (d {x = x}) → Set
Foo x ()
