-- @-patterns from parent clause leaking into with-clause #2303
postulate A : Set

data D : Set where
  c : A → D

data P : D → Set where
  d : (x : A) → P (c x)

g : (x : D) → P x → D
g blargh (d y) with Set
g glurph (d y) | w = {!!}
  -- Expected: glurph = c y : D, y : A, w : Set₁

h : D → D
h x@(c y) with Set
h (c z) | w = {!!}
  -- Expected: z : A, w : Set₁
