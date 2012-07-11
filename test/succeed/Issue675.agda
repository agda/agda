-- {-# OPTIONS -v scope.operators:100 #-}
module Issue675 where

data D : Set where
  d : D → D

Foo : {x : D} → Set₁
Foo {x = D.d x} = Set
-- qualified constructors should also work in hidden arguments
