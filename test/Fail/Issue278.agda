{-# OPTIONS --warning=error #-}

module Issue278 where

open import Agda.Builtin.Equality

abstract
  module A where
    Foo : Set₁
    Foo = Set
  module B where
    open A
    Foo≡Set : Foo ≡ Set
    Foo≡Set = refl
