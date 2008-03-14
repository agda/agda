------------------------------------------------------------------------
-- Decorating star-lists, and looking up elements from them
------------------------------------------------------------------------

module Data.Star.Decoration where

open import Data.Star
open import Data.Maybe
open import Relation.Binary
open import Relation.Binary.Consequences
open import Data.Function
open import Data.Unit
open import Logic

-- A predicate on relation "edges" (think of the relation as a graph).

EdgePred : forall {I} -> Rel I -> Set1
EdgePred T = forall {i j} -> T i j -> Set

-- Decorating an edge with more information.

data DecoratedWith {I : Set} {T : Rel I} (P : EdgePred T)
       : Rel (NonEmpty (Star T)) where
  ↦ : forall {i j k} {x : T i j} {xs : Star T j k} ->
      P x -> DecoratedWith P (nonEmpty (x ◅ xs)) (nonEmpty xs)

edge : forall {I} {T : Rel I} {P : EdgePred T} {i j} ->
       DecoratedWith {T = T} P i j -> NonEmpty T
edge (↦ {x = x} p) = nonEmpty x

decoration : forall {I} {T : Rel I} {P : EdgePred T} {i j} ->
             (d : DecoratedWith {T = T} P i j) ->
             P (NonEmpty.proof (edge d))
decoration (↦ p) = p

-- Star-lists decorated with extra information. All P xs means that
-- all edges in xs satisfy P.

All : forall {I} {T : Rel I} -> EdgePred T -> EdgePred (Star T)
All P {j = j} xs =
  Star (DecoratedWith P) (nonEmpty xs) (nonEmpty {j = j} ε)

trivialAll : forall {I} {T : Rel I} {i j}
             (xs : Star T i j) -> All (\_ -> ⊤) xs
trivialAll ε        = ε
trivialAll (x ◅ xs) = ↦ {x = x} _ ◅ trivialAll xs

-- We can append Alls. Unfortunately _◅◅_ does not quite work.

infixr 5 _◅◅◅_ _▻▻▻_

_◅◅◅_ : forall {I} {T : Rel I} {P : EdgePred T}
               {i j k} {xs : Star T i j} {ys : Star T j k} ->
        All P xs -> All P ys -> All P (xs ◅◅ ys)
ε          ◅◅◅ ys = ys
(↦ x ◅ xs) ◅◅◅ ys = ↦ x ◅ xs ◅◅◅ ys

_▻▻▻_ : forall {I} {T : Rel I} {P : EdgePred T}
               {i j k} {xs : Star T j k} {ys : Star T i j} ->
        All P xs -> All P ys -> All P (xs ▻▻ ys)
_▻▻▻_ = flip _◅◅◅_

-- Pointers into star-lists. The edge pointed to is decorated with Q,
-- while other edges are decorated with P.

data Pointer {I : Set} {T : Rel I} (P Q : EdgePred T)
       : Rel (Maybe (NonEmpty (Star T))) where
  step : forall {i j k} {x : T i j} {xs : Star T j k} ->
         P x -> Pointer P Q (just (nonEmpty (x ◅ xs)))
                            (just (nonEmpty xs))
  done : forall {i j k} {x : T i j} {xs : Star T j k} ->
         Q x -> Pointer P Q (just (nonEmpty (x ◅ xs))) nothing

-- Any P Q xs means that some edge in xs satisfies Q, while all
-- preceding edges satisfy P. A star-list of type Any Always Always xs
-- is basically a prefix of xs; the existence of such a prefix
-- guarantees that xs is non-empty.

Any : forall {I} {T : Rel I} (P Q : EdgePred T) -> EdgePred (Star T)
Any P Q xs = Star (Pointer P Q) (just (nonEmpty xs)) nothing

this : forall {I} {T : Rel I} {P Q : EdgePred T}
              {i j k} {x : T i j} {xs : Star T j k} ->
       Q x -> Any P Q (x ◅ xs)
this q = done q ◅ ε

that : forall {I} {T : Rel I} {P Q : EdgePred T}
       {i j k} {x : T i j} {xs : Star T j k} ->
       P x -> Any P Q xs -> Any P Q (x ◅ xs)
that p = _◅_ (step p)

-- Safe lookup.

data Result {I : Set} (T : Rel I) (P Q : EdgePred T) : Set where
  result : forall {i j} {x : T i j} ->
           P x -> Q x -> Result T P Q

-- The first argument points out which edge to extract. The edge is
-- returned, together with proofs that it satisfies Q and R.

lookup : forall {I} {T : Rel I} {P Q R : EdgePred T}
                {i j} {xs : Star T i j} ->
         Any P Q xs -> All R xs -> Result T Q R
lookup (done q ◅ ε)      (↦ r ◅ _)  = result q r
lookup (step p ◅ ps)     (↦ r ◅ rs) = lookup ps rs
lookup (done _ ◅ () ◅ _) _

-- We can define something resembling init.

prefixIndex : forall {I} {T : Rel I} {P Q : EdgePred T}
                     {i j} {xs : Star T i j} ->
              Any P Q xs -> I
prefixIndex (done {i = i} q ◅ _)  = i
prefixIndex (step p         ◅ ps) = prefixIndex ps

prefix : forall {I} {T : Rel I} {P Q : EdgePred T}
                {i j} {xs : Star T i j} ->
         (ps : Any P Q xs) -> Star T i (prefixIndex ps)
prefix (done q         ◅ _)  = ε
prefix (step {x = x} p ◅ ps) = x ◅ prefix ps

-- Here we are taking the initial segment of ps (all elements but the
-- last, i.e. all edges satisfying P).

init : forall {I} {T : Rel I} {P Q : EdgePred T}
              {i j} {xs : Star T i j} ->
       (ps : Any P Q xs) -> All P (prefix ps)
init (done q ◅ _)  = ε
init (step p ◅ ps) = ↦ p ◅ init ps

-- One can simplify the implementation by not carrying around the
-- indices in the type:

data NonEmptyEdgePred {I : Set} (T : Rel I) (P : EdgePred T) : Set where
  nonEmptyEdgePred : forall {i j} {x : T i j} ->
                     P x -> NonEmptyEdgePred T P

last : forall {I} {T : Rel I} {P Q : EdgePred T}
              {i j} {xs : Star T i j} ->
       Any P Q xs -> NonEmptyEdgePred T Q
last ps with lookup ps (trivialAll _)
... | result q _ = nonEmptyEdgePred q
