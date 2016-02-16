
open import Common.Reflection
open import Common.Unit
open import Common.Prelude

macro

  t1 : (A : Set) -> Term -> Term -> Tactic
  t1 x y z = give y

  t2 : Term -> (A : Set) -> Term -> Tactic
  t2 x y z = give x

  t3 : Term -> Term -> (A : Set) -> QName -> Tactic
  t3 x y z n = give x

  t4 : Term -> Term -> (A : Set) -> A -> Tactic
  t4 x y z a = give x


f1 : {A : Set} -> A -> A
f1 x = t1 Unit x x

f2 : {A : Set} -> A -> A
f2 x = t2 x Unit x

y : Set
y = Unit

f3 : {A : Set} -> A -> A
f3 x = (t3 x x Unit y)

f4 : {A : Set} -> A -> A
f4 x = t4 x x Unit unit
