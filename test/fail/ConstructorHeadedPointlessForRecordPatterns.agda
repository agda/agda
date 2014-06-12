-- Andreas, 2014-06-12
-- No inversion on one clause functions with record patterns only!

{-# OPTIONS -v tc.inj:40 #-} -- KEEP!

module _ where

open import Common.Product

-- No inverse should be created for swap by
-- checkInjectivity, since we are dealing with a record constructor.
swap : ∀{A B} → A × B → B × A
swap (a , b) = b , a

-- The internal representation is
--
--   swap p = (snd p, fst p)
--
-- so trying to use injectivity is pointless here.

-- The expected output should mention that injectivity for swap is pointless.
-- ...
-- Injectivity of ConstructorHeadedPointlessForRecordPatterns.swap would be pointless.

-- Crash after typechecking swap.  KEEP!
CRASH : Set
CRASH = Set
