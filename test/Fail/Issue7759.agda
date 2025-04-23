-- Andreas, 2025-04-07, issue #7759, reported and test case by nad
--
-- Too few with-patterns lead to wrong calculation of the "with-substitution"
-- and subsequently an internal error when accessing the meta-variable
-- thus transported into the wrong context.
--
-- The remedy is to install a check for sufficiently many with-patterns
-- in the type checker, so that we are not entirely at the mercy
-- of syntactic checks in the nicifier.
-- In the present case, such a check was deactivated by
-- 86b3223c477ca9f640eacddab2696bfd7c387b50 deemed to be just a refactoring:
-- [ re #4704 ] Refactor: new way to track ellipsis in concrete syntax

-- {-# OPTIONS -v tc.decl:10 #-}
-- {-# OPTIONS -v tc.with:50 #-}
-- {-# OPTIONS -v tc.def:50 #-}
-- {-# OPTIONS -v tc:10 #-}
-- {-# OPTIONS -v tc.lhs.top:30 #-}

data Eq (A : Set) (a : A) : A → Set where
  refl : Eq A a a

f : (A : Set) (a : A) → Eq (Eq A a a) refl refl
f A a with f A _
... = refl

-- WAS: internal error that could be triggered early by tc.lhs.top:20.
--
-- Error NOW:
-- Too few arguments given in with-clause
-- when checking that the clause
-- f A a with f A _
-- f A a = refl
-- has type (A : Set) (a : A) → Eq (Eq A a a) refl refl
