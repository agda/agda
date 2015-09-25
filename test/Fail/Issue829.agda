-- {-# OPTIONS -v tc.cover.splittree:10 -v tc.cc:30 #-}
module Issue829 where

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

postulate
  P : ⊥ → Set

data D : (A : Set) → A → Set where
  c : ⊥ → (x : ⊤) → D ⊤ x

f : {A : Set} {x : A} → D A x → ⊥
f (c () .tt)

g : (x : ⊥) → P x
g ()

h : (A : Set) (x : A) (d : D A x) → P (f d)
h .⊤ tt (c x .tt) = g x

-- Bug.agda:21,21-24
-- Incomplete pattern matching when applying Bug.f
-- when checking that the expression g x has type P (f (c x tt))

-- Agda 2.3.2 gives the following more reasonable error message:
--
-- Bug.agda:21,21-24
-- x != f (c x tt) of type ⊥
-- when checking that the expression g x has type P (f (c x tt))

-- This regression is caused by the patch "Fixed  issue 827 : incomplete
-- case tree caused by record pattern translation".
