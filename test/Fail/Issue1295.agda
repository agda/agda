-- Andreas, 2014-10-09, issue reported by jesper.cockx

open import Common.Product

pattern foo x = x , x
-- Should complain about non-linearity.

test : {A : Set} → A × A → A
test (foo x) = x
