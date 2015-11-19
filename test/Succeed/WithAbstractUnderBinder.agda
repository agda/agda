-- Andreas, 2015-02-07

-- {-# OPTIONS -v tc.with:40 #-}

open import Common.Prelude hiding (not)

not : Bool → Bool
not true = false
not false = true

T : Bool → Set → Set
T true  A = A → A
T false A = Bool

test : (b : Bool) → (A : Set) → T (not b) A
test b with not b
test b | true   = λ A a → a
test b | false  = λ A → false

-- should be able to abstract (not b) under Binder (A : Set)
-- and succeed
