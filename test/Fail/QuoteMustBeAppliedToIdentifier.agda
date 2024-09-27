-- Andreas, 2024-09-27
-- Trigger error "quote must be applied to an identifier".

test : Set → Set₁
test quote = Set

-- `quote' expects an unambiguous defined name, but here the argument is missing
-- when scope checking the left-hand side test quote in the definition of test
