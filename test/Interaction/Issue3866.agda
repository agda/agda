{-# OPTIONS --no-unicode #-}

data Two : Set where
  tt ff : Two

data Foo : Set where
  foo : Foo -> Foo -> Foo

test1 : Foo → Two
test1 x₀ = {!!}

test : Foo -> Foo → Two
test x1 = {!!}
