{-# OPTIONS --prop #-}

{-# TERMINATING #-}
makeloop : {P : Prop} → P → P
makeloop p = makeloop p

postulate
  A : Set
  B C : A → Prop

record AB : Set where
  no-eta-equality  -- the problem goes away if this is left out
  constructor _,_
  field
    a : A
    b : B a
open AB public

-- -- Same problem if replacing the no-eta record by a datatype
-- data AB : Set where
--   _,_ : (a : A) → B a → AB

-- a : AB → A
-- a (x , y) = x

-- b : (z : AB) → B (a z)
-- b (x , y) = y

record ABC : Set where
  constructor _,_
  field
    ab : AB
    c : C (a ab)  -- the problem goes away if this field is left out
open ABC public

f : AB → ABC
f ab = (a ab , makeloop (b ab)) , {!!}

postulate
  P : ABC → Prop
  g : (ab : AB) → P (f ab)

works : (ab : AB) → P (f ab)
works ab = g ab

loops : (ab : AB) → P (f ab)
loops ab = g _

-- WAS: Agda loops while typechecking @loops@
-- SHOULD: succeed (with unsolved metas)
