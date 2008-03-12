------------------------------------------------------------------------
-- Decorating star-lists, and looking up elements from them
------------------------------------------------------------------------

module Data.Star.Decoration where

open import Data.Star
open import Data.Maybe
open import Relation.Binary

-- A predicate on relation "edges" (think of the relation as a graph).

EdgePred : forall {I} -> Rel I -> Set1
EdgePred T = forall {i j} -> T i j -> Set

-- Decorating an edge with more information.

data DecoratedWith {I : Set} {T : Rel I} (P : EdgePred T)
       : Rel (NonEmpty (Star T)) where
  dec : forall {i j k} {x : T i j} {xs : Star T j k} ->
        P x -> DecoratedWith P (nonEmpty (x ◅ xs)) (nonEmpty xs)

-- Star-lists decorated with extra information. All P xs means that
-- all edges in xs satisfy P.

All : forall {I} {T : Rel I} -> EdgePred T -> EdgePred (Star T)
All P {j = j} xs =
  Star (DecoratedWith P) (nonEmpty xs) (nonEmpty {j = j} ε)

-- Pointers into star-lists. The edge pointed to is decorated with P.

data Pointer {I : Set} {T : Rel I} (P : EdgePred T)
       : Rel (Maybe (NonEmpty (Star T))) where
  step : forall {i j k} {x : T i j} {xs : Star T j k} ->
         Pointer P (just (nonEmpty (x ◅ xs))) (just (nonEmpty xs))
  done : forall {i j k} {x : T i j} {xs : Star T j k} ->
         P x -> Pointer P (just (nonEmpty (x ◅ xs))) nothing

-- Any P xs means that some edge in xs satisfies P. A star-list of
-- type Any Always xs is basically a prefix of xs; the existence of
-- such a prefix guarantees that xs is non-empty.

Any : forall {I} {T : Rel I} -> EdgePred T -> EdgePred (Star T)
Any P xs = Star (Pointer P) (just (nonEmpty xs)) nothing

this : forall {I} {T : Rel I} {P : EdgePred T}
              {i j k} {x : T i j} {xs : Star T j k} ->
       P x -> Any P (x ◅ xs)
this p = done p ◅ ε

that : forall {I} {T : Rel I} {P : EdgePred T}
       {i j k} {x : T i j} {xs : Star T j k} ->
       Any P xs -> Any P (x ◅ xs)
that = _◅_ step

-- Safe lookup.

data Result {I : Set} (T : Rel I) (P Q : EdgePred T) : Set where
  result : forall {i j} {x : T i j} ->
           P x -> Q x -> Result T P Q

-- The first argument points out which edge to extract. The edge is
-- returned, together with proofs that it satisfies P and Q.

lookup : forall {I} {T : Rel I} {P Q : EdgePred T}
                {i j} {xs : Star T i j} ->
         Any P xs -> All Q xs -> Result T P Q
lookup (done p ◅ ε)      (dec q ◅ _)  = result p q
lookup (step   ◅ ps)     (dec q ◅ qs) = lookup ps qs
lookup (done _ ◅ () ◅ _) _
