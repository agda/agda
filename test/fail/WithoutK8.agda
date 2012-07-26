{-# OPTIONS --without-K #-}

module WithoutK8 where

data I : Set where
  i : I

module M (x : I) where

  data D : Set where
    d : D

  data P : D → Set where

postulate x : I

open module M′ = M x

Foo : P d → Set
Foo ()
