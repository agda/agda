-- Andreas, 2016-06-17, issue #2018 reported by Nisse

-- Shadowing a module parameter with a record parameter
-- caused the record parameter to be renamed

-- {-# OPTIONS -v tc.rec:20 #-}

module _ {A : Set} where

data D {A : Set} : Set where
  c : D

record R {A : Set} : Set where
  constructor rc

postulate
  B : Set

test-c : (B : Set) → D {A = B}
test-c B = c {A = B}

test-rc : (B : Set) → R {A = B}
test-rc B = rc {A = B}

-- Error WAS:
-- Function does not accept argument {A = _}
-- when checking that {A = B} is a valid argument to a function of
-- type {A₁ : Set} → Set

-- Should work now.
