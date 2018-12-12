{-# OPTIONS --guardedness #-}

module Issue906 where

{- Globular types as a coinductive record -}
record Glob : Set1 where
  coinductive
  field
    Ob : Set
    Hom : (a b : Ob) → Glob
open Glob public

record Unit : Set where

data _==_ {A : Set} (a : A) : A → Set where
  refl : a == a

{- The terminal globular type -}
Unit-glob : Glob
Ob Unit-glob = Unit
Hom Unit-glob _ _ = Unit-glob

{- The tower of identity types -}
Id-glob : (A : Set) → Glob
Ob (Id-glob A) = A
Hom (Id-glob A) a b = Id-glob (a == b)

-- should termination check
