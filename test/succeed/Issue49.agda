module Issue49 where

module Dummy {A : Set1} where
  postulate D : Set

T : Set
T = Dummy.D {Set}

T' : Set
T' = Dummy.D {A = Set}