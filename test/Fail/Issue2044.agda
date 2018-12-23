
postulate
  T C D : Set
  instance I : {{_ : C}} → D
  d : {{_ : D}} → T

t : T
t = d
