
module Unique where

open import Category

module Uniq (ℂ : Cat) where

  private open module CC = Category.Category ℂ

  -- We say that f ∈! P iff f is the unique arrow satisfying P.
  data _∈!_ {A B : Obj}(f : A ─→ B)(P : A ─→ B -> Set) : Set where
    unique : (forall g -> P g -> f == g) -> f ∈! P

  itsUnique : {A B : Obj}{f : A ─→ B}{P : A ─→ B -> Set} ->
	      f ∈! P -> (g : A ─→ B) -> P g -> f == g
  itsUnique (unique h) = h

  data ∃! {A B : Obj}(P : A ─→ B -> Set) : Set where
    witness : (f : A ─→ B) -> f ∈! P -> ∃! P

  getWitness : {A B : Obj}{P : A ─→ B -> Set} -> ∃! P -> A ─→ B
  getWitness (witness w _) = w

  uniqueWitness : {A B : Obj}{P : A ─→ B -> Set}(u : ∃! P) ->
		  getWitness u ∈! P
  uniqueWitness (witness _ u) = u

  witnessEqual : {A B : Obj}{P : A ─→ B -> Set} -> ∃! P ->
		 {f g : A ─→ B} -> P f -> P g -> f == g
  witnessEqual u {f} {g} pf pg = trans (sym hf) hg
    where
      h = getWitness u

      hf : h == f
      hf = itsUnique (uniqueWitness u) f pf

      hg : h == g
      hg = itsUnique (uniqueWitness u) g pg
