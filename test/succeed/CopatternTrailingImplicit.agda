{-# OPTIONS --copatterns --sized-types #-}
-- Andreas, 2013-10-01 Make sure trailing implicit insertion
-- works with copatterns
module CopatternTrailingImplicit where

import Common.Level
open import Common.Size
open import Common.Prelude

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

-- 2013-10-12 works now also with out manual {_} insertion
-- (See TermCheck.introHiddenLambdas.)
nats' : {i : Size} → Stream Nat {i}
head nats' = 0
tail nats' = map suc nats'
-- Before this latest patch, the termination checker would complain
-- since it would not see the type of the hidden {j : Size< i}
-- which is the argument to the recursive call.

-- All this would not be an issue if Agda still eagerly introduced
-- trailing hidden arguments on the LHS, but this has other
-- drawbacks (Q: even with varying arity?): cannot have
-- hidden lambdas on rhs (used to name trailing hiddens in with-clauses).
