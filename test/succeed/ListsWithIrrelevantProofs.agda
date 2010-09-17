module ListsWithIrrelevantProofs where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

postulate Leq : Nat -> Nat -> Set

-- descending lists indexed by upper bound for largest element 
data SList : Nat -> Set where
  snil  : SList 0
  scons : (head : Nat) -> (bound : Nat) ->
          .(Leq bound head) -> -- irrelevant proof, dotted non-dependent domain
          (tail : SList bound) -> SList head

postulate 
  p1 : Leq 0 1
  p2 : Leq 0 1

l1 : SList 1
l1 = scons 1 0 p1 snil

l2 : SList 1
l2 = scons 1 0 p2 snil
    
data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

-- proofs in list are irrelevant

l1==l2 : l1 == l2
l1==l2 = refl


