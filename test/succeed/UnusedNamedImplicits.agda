-- {-# OPTIONS -v tc.lhs.top:15 -v tc.lhs.unify:100 #-}
-- There was a bug which caused the type checker to forget
-- the name of implicit arguments which weren't used in the
-- return type.
module UnusedNamedImplicits where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- Simple example
f : {n m : Nat} -> Nat
f {m = m} = m

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Even : Nat -> Set where
  evenZ  : Even zero
  evenSS : {n : Nat} -> Even n -> Even (suc (suc n))

index : {n : Nat} -> Even n -> Nat
index  evenZ     = zero
index (evenSS e) = suc (suc (index e))

sameIndex : {n : Nat}(e : Even n) -> index e == n
sameIndex evenZ = refl
sameIndex (evenSS e) with index e | sameIndex e
... | ._ | refl = refl

-- It could also show up when the argument is used in the top level type,
-- but not by the generated type for the with function.
* : {n : Nat}{e : Even n} -> Even (index e)
* {e = e} with index e | sameIndex e
... | ._ | refl = e
