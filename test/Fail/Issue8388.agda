-- Andreas, 2026-02-11, issue #8388, report and test case by Maykeye

module Issue8388 where

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

-- {-# BUILTIN EQUALITY _≡_ #-}  -- needed for with...in
-- {-# BUILTIN REFL refl  #-}    -- deprecated builtin

data T : Set where
    ta : T

postulate
  g :  (a b : T) → a ≡ b

f : (a b : T) → a ≡ b
f a b with g a b in gab
... | q = q

-- WAS: No binding for builtin thing REFL, use {-# BUILTIN REFL name #-} to...

-- Expected error: [NoBindingForBuiltin]
-- No binding for builtin REFL, use {-# BUILTIN EQUALITY name #-} to
-- bind the builtin equality type to 'name'
-- when checking that the clause
-- f a b with gab : g a b
-- ... | q = q
-- has type (a b : T) → a ≡ b
