-- Andreas, 2012-09-13
module RelevanceSubtyping where

-- this naturally type-checks:
one : {A B : Set} → (.A → B) → A → B
one f x = f x

-- this type-checks because of subtyping
one' : {A B : Set} → (.A → B) → A → B
one' f = f
