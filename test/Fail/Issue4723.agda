-- Andreas, 2020-06-03, issue #4723
-- Regression introduced in 2.5.4 due to work on #2822

f : Set₁ → Set₁
f with Set
... | _ = λ _ → Set
... x = x

-- ERROR WAS: Unreachable clause f x = x
-- EXPECTED: This should not parse.
