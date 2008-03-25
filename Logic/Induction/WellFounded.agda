------------------------------------------------------------------------
-- Well-founded induction
------------------------------------------------------------------------

open import Relation.Binary

module Logic.Induction.WellFounded {a : Set} (_<_ : Rel a) where

open import Logic.Induction

-- The accessibility predicate.

data Acc (x : a) : Set where
  acc : (forall {y} -> y < x -> Acc y) -> Acc x

AccRec : RecStruct a
AccRec P x = forall y -> y < x -> P y

-- Standard well-founded induction does not quite fit into the scheme
-- set up in Logic.Induction:

module Some where

  accRec : (P : a -> Set) ->
           (forall x -> AccRec P x -> P x) ->
           forall {x} -> Acc x -> P x
  accRec P f (acc g) = f _ (\_ y<x -> accRec P f (g y<x))

  accRec-builder : (P : a -> Set) ->
                   (forall x -> AccRec P x -> P x) ->
                   forall {x} -> Acc x -> AccRec P x
  accRec-builder P f (acc g) _ y<x = accRec P f (g y<x)

-- However, if _all_ elements are accessible, then it does:

module All (allAcc : forall x -> Acc x) where

  accRec-builder : RecursorBuilder AccRec
  accRec-builder P f x = Some.accRec-builder P f (allAcc x)

  accRec : Recursor AccRec
  accRec = build accRec-builder
