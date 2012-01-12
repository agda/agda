module Issue396b where

import Common.Irrelevance  

data A : Set where

-- just an irrelevant field
record PrfA : Set where
  field
    .f : A

Foo : Set -> Set1
Foo R = (P : R → Set) → ((x : R) → P x → P x) →
                        (x y : R) → P x → P y
foo : Foo PrfA
foo P hyp x y = hyp x
-- Error was:
-- x != y of type ⊤
-- when checking that the expression hyp x has type P x → P y

record Top : Set where

-- only singleton components
record R : Set where
  field
    p1 : PrfA
    .p2 : A
    p3 : Top

bla : Foo R
bla P hyp x y = hyp x
