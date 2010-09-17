module ListsWithIrrelevantProofs where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

postulate 
  _≤_ : ℕ → ℕ → Set
  p1 : 0 ≤ 1
  p2 : 0 ≤ 1

-- descending lists indexed by upper bound for largest element 

data SList (bound : ℕ) : Set where
  []    : SList bound
  scons : (head : ℕ) →
          .(head ≤ bound) →   -- irrelevant proof, dotted non-dependent domain
          (tail : SList head) → 
          SList bound

l1 : SList 1
l1 = scons 0 p1 []

l2 : SList 1
l2 = scons 0 p2 []

-- proofs in list are irrelevant

l1≡l2 : l1 ≡ l2
l1≡l2 = refl


