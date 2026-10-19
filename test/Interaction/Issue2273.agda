-- Jesper, 2018-10-16: When solving constraints, unsolved metas should
-- be turned into interaction holes. Metas that refer to an existing
-- interaction hole should be printed as _ instead.

postulate
  _==_ : {A : Set} (a b : A) → Set
  P : Set → Set
  f : {A : Set} {a : A} {b : A} → P (a == b)

x : P {!!}
x = f

y : P {!!}
y = f {a = {!!}} {b = {!!}}
