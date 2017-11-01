-- Andreas, 2017-11-01, issue #2824
-- Don't allow built-ins defined in parametrized modules

module _ {a} {A : Set a} where

  data _≡_ (x : A) : A → Set a where
    refl : x ≡ x

  {-# BUILTIN EQUALITY _≡_ #-}

-- This is forbidden, could maybe allowed using lambda-lifting.
