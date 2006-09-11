{-# OPTIONS --proof-irrelevance #-}
module Pragma where

postulate
  Foo : Prop
  foo1 : Foo
  foo2 : Foo

  Bar : Foo -> Set

-- Only goes through with proof irrelevance.
f : Bar foo1 -> Bar foo2
f x = x

