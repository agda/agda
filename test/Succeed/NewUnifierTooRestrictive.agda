-- 2016-01-05, Jesper: In some cases, the new unifier is still too restrictive
-- when --without-K is enabled because it doesn't do generalization of datatype
-- indices. This should be fixed in the future.

-- 2016-06-23, Jesper: Now fixed.


{-# OPTIONS --without-K #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Bar : Set₁ where
  bar : Bar
  baz : (A : Set) → Bar

data Foo : Bar → Set where
  foo : Foo bar

test : foo ≡ foo → Set₁
test refl = Set
