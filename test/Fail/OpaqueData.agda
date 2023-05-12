{-# OPTIONS --warning=error #-}
module OpaqueData where

opaque
  data Foo : Set where
    foo : Foo

_ : Foo
_ = Foo.foo
