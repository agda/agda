-- Reported by guillaume.brunerie, Sep 18, 2013
-- Andreas, 2013-10-27  issue submitted by Guilliaume Brunerie

{-# OPTIONS --guardedness #-}

module Issue907 where

-- Globular types as a coinductive record

record Glob : Set1 where
  coinductive
  field
    Ob : Set
    Hom : (a b : Ob) → Glob
open Glob public

Glob-corec : {A : Set1} (Ob* : A → Set)
  (Hom* : (x : A) (a b : Ob* x) → A) → (A → Glob)
Ob  (Glob-corec Ob* Hom* x)     = Ob* x
Hom (Glob-corec Ob* Hom* x) a b = Glob-corec Ob* Hom* (Hom* x a b)

-- For the second equation to type-check,
-- we need to reduce with the first equation!
