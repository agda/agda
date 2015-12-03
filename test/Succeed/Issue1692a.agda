-- Andreas, 2015-11-19 Issue 1692
-- With-abstract also in types of variables mentioned in with-expressions
-- unless they are also mentioned in the types of the with-expressions.

-- {-# OPTIONS -v tc.with:40 #-}

open import Common.Equality

postulate
  A : Set
  a : A

test : (dummy : A) (f : ∀ x → a ≡ x) (b : A) → b ≡ a
test dummy f b rewrite f b = f b

-- WAS:
-- The `a` is not with-abstracted in the type of `f`, as `f` occurs
-- in the rewrite expression `f b : a ≡ b`.

-- NOW: with abstracts also in type of f, changing it to (f : ∀ x → b ≡ x)

test-with : (f : ∀ x → a ≡ x) (b : A) → b ≡ a
test-with f b with a | f b
test-with f b | .b | refl = f b

-- WAS:

-- Manually, we can construct what `magic with` DID not do:
-- abstract `a` also in the type of `f`, even though `f` is part of the
-- rewrite expression.
bla : (f : ∀ x → a ≡ x) (b : A) → b ≡ a
bla f b = aux b a (f b) f
  where
    aux : (b w : A) (p : w ≡ b) (f : ∀ x → w ≡ x) → b ≡ w
    aux b .b refl f = f b
