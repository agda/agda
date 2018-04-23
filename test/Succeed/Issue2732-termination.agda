-- Andreas, 2017-09-09, re issue #2732
-- eta-contraction needed in termination checker

-- {-# OPTIONS -v term:30 #-}

open import Agda.Builtin.Equality

data O (A : Set) : Set where
  leaf : O A
  node : (A → O A) → O A

postulate
  A : Set
  a : A

test1 : (t u : O A) → O A
test1 leaf     leaf     = leaf
test1 leaf     (node g) = test1 leaf (g a)
test1 (node f) leaf     = test1 (f a) (node f)
test1 (node f) (node g) = test1 (node λ x → f x) (g a)
-- Should pass even with the eta-expansion.

data Q (A : Set) : Set where
  leaf : Q A
  node : (f g : A → Q A) (p : f ≡ g) → Q A

-- Having various call arguments in eta-expanded form.
test : (t u : Q A) → Q A
test leaf leaf = leaf
test leaf (node f g p) = test leaf (f a)
test (node f g p) leaf = test (g a) (node f g p)
test (node f .f refl) (node g g' p) = test (node (λ x → f x) _ refl) (g' a)
