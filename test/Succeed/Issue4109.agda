open import Agda.Primitive

data Foo : Setω where
  foo : Foo

bar : Foo → Foo
bar foo = foo
