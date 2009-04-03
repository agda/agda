------------------------------------------------------------------------
-- Pointers into star-lists
------------------------------------------------------------------------

module Data.Star.Pointer where

open import Data.Star
open import Data.Star.Decoration
open import Relation.Binary
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Unit
open import Data.Function

-- Pointers into star-lists. The edge pointed to is decorated with Q,
-- while other edges are decorated with P.

data Pointer {I : Set} {T : Rel I} (P Q : EdgePred T)
       : Rel (Maybe (NonEmpty (Star T))) where
  step : ∀ {i j k} {x : T i j} {xs : Star T j k}
         (p : P x) → Pointer P Q (just (nonEmpty (x ◅ xs)))
                                 (just (nonEmpty xs))
  done : ∀ {i j k} {x : T i j} {xs : Star T j k}
         (q : Q x) → Pointer P Q (just (nonEmpty (x ◅ xs))) nothing

-- Any P Q xs means that some edge in xs satisfies Q, while all
-- preceding edges satisfy P. A star-list of type Any Always Always xs
-- is basically a prefix of xs; the existence of such a prefix
-- guarantees that xs is non-empty.

Any : ∀ {I} {T : Rel I} (P Q : EdgePred T) → EdgePred (Star T)
Any P Q xs = Star (Pointer P Q) (just (nonEmpty xs)) nothing

this : ∀ {I} {T : Rel I} {P Q : EdgePred T}
             {i j k} {x : T i j} {xs : Star T j k} →
       Q x → Any P Q (x ◅ xs)
this q = done q ◅ ε

that : ∀ {I} {T : Rel I} {P Q : EdgePred T}
       {i j k} {x : T i j} {xs : Star T j k} →
       P x → Any P Q xs → Any P Q (x ◅ xs)
that p = _◅_ (step p)

-- Safe lookup.

data Result {I : Set} (T : Rel I) (P Q : EdgePred T) : Set where
  result : ∀ {i j} {x : T i j}
           (p : P x) (q : Q x) → Result T P Q

-- The first argument points out which edge to extract. The edge is
-- returned, together with proofs that it satisfies Q and R.

lookup : ∀ {I} {T : Rel I} {P Q R : EdgePred T}
               {i j} {xs : Star T i j} →
         Any P Q xs → All R xs → Result T Q R
lookup (done q ◅ ε)      (↦ r ◅ _)  = result q r
lookup (step p ◅ ps)     (↦ r ◅ rs) = lookup ps rs
lookup (done _ ◅ () ◅ _) _

-- We can define something resembling init.

prefixIndex : ∀ {I} {T : Rel I} {P Q : EdgePred T}
                    {i j} {xs : Star T i j} →
              Any P Q xs → I
prefixIndex (done {i = i} q ◅ _)  = i
prefixIndex (step p         ◅ ps) = prefixIndex ps

prefix : ∀ {I} {T : Rel I} {P Q : EdgePred T} {i j} {xs : Star T i j} →
         (ps : Any P Q xs) → Star T i (prefixIndex ps)
prefix (done q         ◅ _)  = ε
prefix (step {x = x} p ◅ ps) = x ◅ prefix ps

-- Here we are taking the initial segment of ps (all elements but the
-- last, i.e. all edges satisfying P).

init : ∀ {I} {T : Rel I} {P Q : EdgePred T} {i j} {xs : Star T i j} →
       (ps : Any P Q xs) → All P (prefix ps)
init (done q ◅ _)  = ε
init (step p ◅ ps) = ↦ p ◅ init ps

-- One can simplify the implementation by not carrying around the
-- indices in the type:

last : ∀ {I} {T : Rel I} {P Q : EdgePred T}
             {i j} {xs : Star T i j} →
       Any P Q xs → NonEmptyEdgePred T Q
last ps with lookup ps (decorate (const tt) _)
... | result q _ = nonEmptyEdgePred q
