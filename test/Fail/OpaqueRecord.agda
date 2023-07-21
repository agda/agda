{-# OPTIONS --warning=error #-}
module OpaqueRecord where

opaque
  record Foo : Set where
    inductive
    field
      foo : Foo

_ : Foo → Foo
_ = Foo.foo
