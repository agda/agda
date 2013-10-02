{-# OPTIONS --copatterns --sized-types --experimental-irrelevance #-}
-- Andreas, 2013-10-01 Make sure trailing implicit insertion
-- works with copatterns
module CopatternTrailingImplicit where

import Common.Level
open import Common.Size
open import Common.Prelude

postulate
  Size< : ..(_ : Size) → Set
{-# BUILTIN SIZELT Size< #-}

-- Sized streams

record Stream (A : Set) {i : Size} : Set where
  coinductive
  field
    head : A
    tail : {j : Size< i} → Stream A {j}
open Stream

-- Mapping over streams

map : {A B : Set} (f : A → B) {i : Size} → Stream A {i} → Stream B {i}
head (map f s) = f (head s)
tail (map f s) = map f (tail s)

-- Nats defined using map
nats : {i : Size} → Stream Nat {i}
head nats = 0
tail nats {_} = map suc nats
-- Before this patch, Agda would insert a {_} also in the `head' clause
-- leading to a type error.
