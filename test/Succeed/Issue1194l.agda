  module _ where

  module A where

    postulate C : Set → Set → Set

    syntax C X Y = X , Y

  module B where

    postulate C : Set

  open A
  open B

  Foo : Set → Set
  Foo X = X , X
