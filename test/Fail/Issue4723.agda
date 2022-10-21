-- Andreas, 2022-09-25, test case to track #4723

f : Set₁ → Set₁
f with Set
... | _ = λ _ → Set
... x = x

-- Ideally, this would give a parse error,
-- but at least, it should give some error rather than crashing.
