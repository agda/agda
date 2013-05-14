-- {-# OPTIONS -v term:20 #-}
module Issue847 where

data ⊥ : Set where

foo : ⊥
foo = bar where
 abstract
  bar : ⊥
  bar = foo
