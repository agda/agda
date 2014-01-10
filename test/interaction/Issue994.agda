-- {-# OPTIONS -v interaction:50 #-}

x : Set → Set
x = {!λ x → x!}

-- "refine" (C-c C-r) should behave the same as "give" here
-- Old, bad result:
-- x = λ x₁ → x₁
-- New, expected result:
-- x = λ x → x

-- Expected interaction test case behavior:
--
--   (agda2-give-action 0 'no-paren)
