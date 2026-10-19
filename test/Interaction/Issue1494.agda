module Issue1494 where

open import Issue1494.Helper

module M (r : Record) where

  open Module r

  postulate
    A   : Set
    a b : A

  Foo : a ≡ b
  Foo = {!!}
