
data D : Set where
  c : D
  s : D → D

predD : D → D
predD c = c
predD (s x) = x

f : D → D
f c = c
f (s n) with c
f x@(s _) | c = x
f (s _)   | s _ = c

data E : D → Set where
  e : E c
  s : ∀ {x} → E x → E (s x)

predE : ∀ {d} → E d → E (predD d)
predE e     = e
predE (s x) = x

g : ∀ {d} → E d → E (predD d)
g e = e
g (s x) with x
g y@(s _) | s z = predE y
g (s z@e) | e   = predE z
