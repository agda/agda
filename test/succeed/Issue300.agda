{-# OPTIONS  --sized-types --show-implicit #-}
-- {-# OPTIONS -v tc.size.solve:20 #-}
module Issue300 where

open import Common.Size

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {↑ size}
  suc  : {size : Size} -> Nat {size} -> Nat {↑ size}

-- Size meta used in a different context than the one created in

A : Set1
A = (Id : {i : Size} -> Nat {_} -> Set)
    (k : Size)(m : Nat {↑ k}) -> Id {k} m
    ->
    (j : Size)(n : Nat {j}) -> Id {j} n
-- should solve _ with ↑ i
