-- Andreas, 2016-12-20, issue #2350
-- Agda ignores a wrong instance parameter to a constructor

data D {{a}} (A : Set a) : Set a where
  c : A → D A

test : ∀ {{ℓ}} {{ℓ'}} (A : Set ℓ') {B : Set ℓ} (a : A) → D A
test {{ℓ}} A a = c {{ℓ}} a

-- Expected Error:
-- .ℓ' != ℓ of type .Agda.Primitive.Level
-- when checking that the expression a has type A
