-- Andreas, 2025-04-17, issue #7803, report and test case by Szumi Xie
-- Regression introduced by #7539 which turned a generic error into an internal error.

{-# OPTIONS --cubical #-}

-- {-# OPTIONS -v tc.with.abstract:30 #-}
-- {-# OPTIONS -v tc.tel.path:40 #-}

open import Agda.Builtin.Cubical.Path

p : Set ≡ Set
p i with _
... | _ = Set

-- Expected error: [PathAbstractionFailed]
-- Path abstraction failed for type _4 (i = i) → Set₁.
-- The type may be non-fibrant or its sort depends on an interval variable
-- when checking that the clause
-- p i with _
-- ... | _ = Set
-- has type Set ≡ Set
