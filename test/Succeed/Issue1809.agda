{-# OPTIONS -v tc.lhs.unify:80 #-}
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

postulate
  A : Set
  a : A

record Foo : Set where
  constructor foo
  field anA : A

test : (f : A → A) (x : Foo) → foo (f a) ≡ x → A
test f .(foo (f a)) refl = a
