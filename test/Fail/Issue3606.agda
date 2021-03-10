
postulate
  A : Set
  P : A → Set

record ΣAP : Set where
  no-eta-equality
  field
    fst : A
    snd : P fst
open ΣAP

test : (x : ΣAP) → P (fst x)
test x = snd {!!}
