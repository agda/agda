-- Andreas, 2023-01-13, issue #6434
-- This test/Succeed/Issue1086.agda made to fail by --performance:absurd-clauses

{-# OPTIONS --performance:absurd-clauses #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

and : (a b : Bool) → Bool
and true  b = b
and false b = false

test : ∀ a b → and a b ≡ true → a ≡ true
test true true refl = refl

-- Expected error:
--
-- Incomplete pattern matching for test. Missing cases:
--   test false b x
--   test true false x
