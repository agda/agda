module OpaqueData where

opaque
  data Foo : Set where
    foo : Foo

opaque unfolding (Foo.foo) where
  _ : Foo
  _ = Foo.foo
