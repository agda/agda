-- Andreas, 2012-09-13
-- (The signature on the previous line does not apply to all of the
-- text in this file.)
module RelevanceSubtyping where

-- this naturally type-checks:
one : {A B : Set} → (.A → B) → A → B
one f x = f x

-- Subtyping is no longer supported for irrelevance, so the following
-- code is no longer accepted.

-- -- this type-checks because of subtyping
-- one' : {A B : Set} → (.A → B) → A → B
-- one' f = f
