module Issue6627 where

record Foo : Set where
record Bar ⦃ _ : Foo ⦄ : Set where
postulate
  i : Foo
  b : Bar ⦃ i ⦄

open Bar b
