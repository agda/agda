
module Issue512 where

postulate
  Level : Set

{-# BUILTIN LEVEL Level #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

data A : Set where
  a b : A

proof : a ≡ a
proof = refl

f : A → A → A
f x y rewrite proof = ? -- gave error below (now complains about LEVELZERO instead of STRING)

{-
{-
No binding for builtin thing STRING, use {-# BUILTIN STRING name
#-} to bind it to 'name'
when checking that the type of the generated with function
(w : A) → _≡_ {"Max []"} {A} w w → (x y : A) → A is well-formed
-}
-}
