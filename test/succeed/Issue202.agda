{-# OPTIONS --universe-polymorphism --allow-unsolved-metas --no-termination-check #-}

module Issue202 where

Foo : ∀ {A} → A → Set
Foo x = Foo x

-- Previously resulted in the following (cryptic) error:
-- Bug.agda:6,13-14
-- _5 !=< _5
-- when checking that the expression x has type _5