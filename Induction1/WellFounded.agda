------------------------------------------------------------------------
-- Well-founded induction
------------------------------------------------------------------------

-- I want universe polymorphism.

open import Relation.Binary

module Induction1.WellFounded {a : Set} (_<_ : Rel a) where

open import Induction1

-- When using well-founded recursion you can recurse arbitrarily, as
-- long as the arguments become smaller, and "smaller" is
-- well-founded.

WfRec : RecStruct a
WfRec P x = ∀ y → y < x → P y

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.

data Acc (x : a) : Set₁ where
  acc : (rs : WfRec Acc x) → Acc x

-- Well-founded induction for the subset of accessible elements:

module Some where

  wfRec-builder : SubsetRecursorBuilder Acc WfRec
  wfRec-builder P f x (acc rs) = λ y y<x →
    f y (wfRec-builder P f y (rs y y<x))

  wfRec : SubsetRecursor Acc WfRec
  wfRec = subsetBuild wfRec-builder

-- Well-founded induction for all elements, assuming they are all
-- accessible:

module All (allAcc : ∀ x → Acc x) where

  wfRec-builder : RecursorBuilder WfRec
  wfRec-builder P f x = Some.wfRec-builder P f x (allAcc x)

  wfRec : Recursor WfRec
  wfRec = build wfRec-builder
