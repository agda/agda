------------------------------------------------------------------------
-- Looking up elements in reflexive transitive closures
------------------------------------------------------------------------

module Data.Star.Lookup where

open import Data.Star
open import Data.Maybe
open import Relation.Binary

-- A NonEmptyPrefix is a pointer into a star-list.

data NonEmptyPrefixRel {I : Set} (T : Rel I)
       : Rel (Maybe (NonEmpty (Star T))) where
  step : forall {i j k} {x : T i j} {xs : Star T j k} ->
         NonEmptyPrefixRel T (just (nonEmpty (x ◅ xs)))
                             (just (nonEmpty xs))
  done : forall {i j k} {x : T i j} {xs : Star T j k} ->
         NonEmptyPrefixRel T (just (nonEmpty (x ◅ xs)))
                             nothing

NonEmptyPrefixOf : forall {I} {T : Rel I} {i j} -> Star T i j -> Set
NonEmptyPrefixOf {T = T} xs =
  Star (NonEmptyPrefixRel T) (just (nonEmpty xs)) nothing

this : forall {I} {T : Rel I} {i j k} {x : T i j} {xs : Star T j k} ->
       NonEmptyPrefixOf (x ◅ xs)
this = done ◅ ε

that : forall {I} {T : Rel I} {i j k}
       {x : T i j} {xs : Star T j k} ->
       NonEmptyPrefixOf xs -> NonEmptyPrefixOf (x ◅ xs)
that = _◅_ step

-- Safe lookup.

lookup : forall {I} {T : Rel I} {i j}
         (xs : Star T i j) -> NonEmptyPrefixOf xs -> NonEmpty T
lookup (x ◅ xs) (done ◅ ε)  = nonEmpty x
lookup (x ◅ xs) (step ◅ ys) = lookup xs ys

lookup (x ◅ xs) (done ◅ () ◅ _)
lookup ε        (()   ◅ _)
