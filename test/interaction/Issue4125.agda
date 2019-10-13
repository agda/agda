-- Andreas, 2019-10-13, issue 4125
-- Avoid unnecessary normalization in type checker.
-- Print to the user what they wrote, not its expanded form.

-- {-# OPTIONS -v tc:25 #-}

postulate
  We-do-not-want-to : Set → Set
  see-this-in-the-output : Set

A = We-do-not-want-to see-this-in-the-output

postulate
  P : A → Set

test : ∀{a} → P a → P a
test p = {!!} -- C-,

-- Expected to see
--   a : A
-- in the context, not the expanded monster of A.
