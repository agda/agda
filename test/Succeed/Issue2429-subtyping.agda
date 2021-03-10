{-# OPTIONS --subtyping #-}

-- Andreas, 2017-01-24, issue #2429
-- Respect subtyping also for irrelevant lambdas!

-- Subtyping: (.A → B) ≤ (A → B)
-- Where a function is expected, we can put one which does not use its argument.

id : ∀{A B : Set} → (.A → B) → A → B
id f = f

test : ∀{A B : Set} → (.A → B) → A → B
test f = λ .a → f a

-- Should work!
-- The eta-expansion should not change anything!
