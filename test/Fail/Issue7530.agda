{-# OPTIONS --show-implicit #-}

open import Agda.Builtin.Equality

variable
  A B : Set

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : A × B → A
fst (x , y) = x

snd : A × B → B
snd (x , y) = y

-- Force a type error that shows that A and B are dropped
err : (p : A × A) → fst p ≡ snd p
err p = refl

-- When not projection-like (bad):
-- Issue7530.agda:19.9-13: error: [UnequalTerms]
-- fst {A} {A} p != snd {A} {A} p of type A
-- when checking that the expression refl has type
-- _≡_ {Agda.Primitive.lzero} {A} (fst {A} {A} p) (snd {A} {A} p)

-- When projection-like (expected):
-- Issue7530.agda:19.9-13: error: [UnequalTerms]
-- fst p != snd p of type A
-- when checking that the expression refl has type
-- _≡_ {Agda.Primitive.lzero} {A} (fst p) (snd p)
