{-# OPTIONS --cubical --allow-unsolved-metas #-}
module TranspPiOnMeta where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path


-- Transporting along a function type with unknown sort of
-- domain/codomain shouldn't result into an impossible being thrown.

-- We equate to Set to trigger reduction.


test1 : (primTransp (\ i → (x : {!!}) → {!!}) i0 {!!} {!!}) ≡ Set
test1 i = Set


test2 : (primTransp (\ i → (x : Set) → {!!}) i0 {!!} {!!}) ≡ Set
test2 i = Set

Foo : Set₂
Foo = {!!}

test3 : (primTransp (\ i → (x : {!!}) → Foo) i0 {!!} {!!}) ≡ Set
test3 i = Set
