------------------------------------------------------------------------
-- Heterogeneous collections
------------------------------------------------------------------------

module Data.HeterogeneousCollection (Index : Set) where

-- Contexts, listing the indices of the types of all the elements in
-- a collection.

infixl 20 _▻_

data Ctxt : Set where
  nil : Ctxt
  _▻_ : Ctxt -> Index -> Ctxt

-- Labels pointing into a collection. The labels are defined with
-- respect to a given context, and have certain indices.

data Label : Ctxt -> Index -> Set where
  lz : forall {Γ i}    -> Label (Γ ▻ i) i
  ls : forall {Γ i i'} -> Label Γ i -> Label (Γ ▻ i') i

-- Collections. The T function maps indices to element types.

infixl 20 _▷_

data Coll (T : Index -> Set) : Ctxt -> Set where
  ∅   : Coll T nil
  _▷_ : forall {Γ i} -> Coll T Γ -> T i -> Coll T (Γ ▻ i)

-- A safe lookup function for collections.

lookup :  forall {Γ i} {T : Index -> Set}
       -> Label Γ i -> Coll T Γ -> T i
lookup ()     ∅
lookup lz     (ρ ▷ p) = p
lookup (ls l) (ρ ▷ p) = lookup l ρ
