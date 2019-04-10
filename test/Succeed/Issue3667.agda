
data Unit : Set where
  unit : Unit

P : Unit → Set
P unit = Unit

postulate
  Q : (u : Unit) → P u → Set

variable
  u : Unit
  p : P u

postulate
  q : P u → Q u p

q' : (u : Unit) (p : P u) → P u → Q u p
q' u p = q {u} {p}
