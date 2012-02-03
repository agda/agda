
module Issue530 where

data Unit : Set where
  unit : Unit

postulate
  A : Set
  a : A
  k : A → Unit

data P (a : A) : Unit → Set where
  p : P a (k a)

F : (u : Unit) → P a u → Set₁
F unit _ = Set

f : F (k a) p
f with k a
f | _ = ?