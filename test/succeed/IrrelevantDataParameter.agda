{-# OPTIONS --experimental-irrelevance #-}
-- Andreas, 2011-04-15
-- {-# OPTIONS -v tc.data:20 #-}
module IrrelevantDataParameter where

postulate 
  A : Set

data K .(a : A) : Set where
  c : K a

postulate
  a : A

data K' .(b : A) : Set where
  c : K' a
-- ok, since parameter irrelevant

-- 2011-09-09

postulate
  _×_ : ..(A B : Set) -> Set
  Lst : ..(A : Set) -> Set
  nl  : .(A : Set) -> Lst A
  cns : .(A : Set) -> A × Lst A -> Lst A
  -- cns' : .(A : Set) -> (a : A) -> (as : Lst A) -> Lst A -- not well-formed!