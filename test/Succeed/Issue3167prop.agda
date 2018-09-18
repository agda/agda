-- Andreas, 2018-09-12, issue #3167-2: --(no-)prop option
--
-- A local --prop option should override a global --no-prop flag.
-- Issue3167prop.flags has --no-prop.

{-# OPTIONS --prop #-}

-- The following depends on Prop enabled

data _≡_ {a} {A : Prop a} (x : A) : A → Prop a where
  refl : x ≡ x

data P : Prop where
  a b : P

test : (x y : P) → x ≡ y
test x y = refl
