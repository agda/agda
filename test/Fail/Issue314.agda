
module Issue314 where

postulate A : Set

data _≡_ (x : A) : A → Set where
  refl : x ≡ x

postulate lemma : (x y : A) → x ≡ y

Foo : A → Set₁
Foo x with lemma x _
Foo x | refl = Set

-- Bug.agda:12,9-13
-- Failed to solve the following constraints:
--   x == _23 x : A
-- when checking that the pattern refl has type x ≡ _23 x
