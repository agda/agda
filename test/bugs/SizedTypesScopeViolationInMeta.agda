{-# OPTIONS  --sized-types --show-implicit #-} 

module SizedTypesScopeViolationInMeta where

open import Size

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {↑ size}
  suc  : {size : Size} -> Nat {size} -> Nat {↑ size}

-- exposing a bug in size constraint solving

-- *** Exception: Inconsistent meta: _73 [[CtxId 420],[CtxId 418]]
A : Set1
A = (Id : {i : Size} -> Nat {_} -> Set)
    (k : Size)(m : Nat {↑ k}) -> Id {k} m 
    ->
    (j : Size)(n : Nat {j}) -> Id {j} n 

{-
mutual

--   id : {i : Size} -> Nat {_} -> Nat {i}  -- FAILS
  id : {i : Size} -> Nat {i} -> Nat {i} 
  id x = x

  succ : {i : Size} -> Nat {i} -> Nat {↑ i}
  succ x = suc (id x)
-}
