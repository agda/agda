-- Andreas, 2016-07-06, issue #2076 reported by Andrea
-- This is to test printing of extended lambdas

-- {-# OPTIONS -v tc.cc:60 -v tc.term.exlam:100 -v reify.clause:60 #-}

postulate
  A : Set
  _,_ : A → A → A

data Unit : Set where
  true : Unit

bar : (p : A) (q : A) → Unit → A
bar p q = aux
  where
  aux : Unit → A
  aux true = p , q

foo : (p : A) (q : A) → Unit → A
foo p q = \ { true → p , q}

test : (a : A) → Unit → A
test a = foo a a
-- Normalize me! Expected:
-- λ a → λ { true → a , a }

-- From test/interaction/ExtendedLambdaCase.agda

data Bool : Set where
  true false : Bool

data Void : Set where

module M {A : Set}(B : A → Set) where
  postulate
    Bar : (Bool → Bool) → Set

Test : Set
Test = (y : Bool) → M.Bar {Bool} (λ _ → Void) (λ { true → true ; false → false })
-- Normalize me! Expected:
-- (y : Bool) → M.Bar (λ _ → Void) (λ { true → true ; false → false })

-- .extendedlambda1 y true  = true
-- .extendedlambda1 y false = false
-- dropped args:  []
-- hidden  args:  []
-- visible args:  [y]
