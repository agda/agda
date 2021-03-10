{-# OPTIONS --prop --allow-unsolved-metas #-}

{-# TERMINATING #-}
makeloop : {P : Prop} → P → P
makeloop p = makeloop p

postulate
  A : Set
  B : A → Prop

record AB : Set where
  constructor _,_
  field
    a : A
    b : B a
open AB public

id : AB → AB
id ab = a ab , makeloop (b ab)

postulate
  f : (id* : AB → AB) → A → Set

C : A → Set
C = f id

postulate
  D : (C : A → Set) (a : A) (c : C a) → Set

-- Works if you either give the type of v (C u) or the second argument of D (u)
loops : (u : A) (v : _) → D C _ v
loops = {!!}
