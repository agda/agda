-- Andreas, 2017-01-12, issue #2386

id : {A : Set} → A → A
id x = x

data Eq (A : Set) : (x y : A) → Set where
  refl : (x : A) → Eq A x (id x)

{-# BUILTIN EQUALITY Eq #-}

-- Should be accepted.
