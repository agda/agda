
data Unit : Set where
  unit : Unit

F : Unit → Set₁
F unit = Set

data D (u : Unit) (f : F u) : Set where

variable
  u : Unit
  f : F u
  d : D u f

postulate
  P : {u : Unit} {f : F u} → D u f → Set
  p : P d

p' : (u : Unit) (f : F u) (d : D u f) → P d
p' u f d = p {u} {f}  {d}
