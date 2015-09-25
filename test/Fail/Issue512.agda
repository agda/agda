
module Issue512 where

open import Common.Equality

data A : Set where
  a b : A

proof : a ≡ a
proof = refl

f : A → A → A
f x y rewrite proof = {!!}

-- gave error below (now complains about LEVELZERO instead of STRING):
-- No binding for builtin thing STRING, use {-# BUILTIN STRING name #-} to bind it to 'name'
-- when checking that the type of the generated with function
-- (w : A) → _≡_ {"Max []"} {A} w w → (x y : A) → A is well-formed

-- Andreas, 2014-05-17: After fixing 1110, there is no error any more,
-- just an unsolved meta.
