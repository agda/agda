
module _ where

module Foo where
  pattern pat x = x

foo : Set
foo = {!Foo!}
