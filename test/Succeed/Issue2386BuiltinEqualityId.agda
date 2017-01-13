-- Andreas, 2017-01-12, issue #2386

id : ∀{a}{A : Set a} → A → A
id x = x

data Eq (A : Set) : (x y : id A) → Set where
  refl : (x : A) → Eq A x x

{-# BUILTIN EQUALITY Eq #-}

-- Should be accepted.
