{-# OPTIONS --show-implicit #-}

module PragmasRespected where

postulate
  Foo : {A : Set₁} → Set
  Bar : Foo {A = Set}
