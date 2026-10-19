-- Andreas, 2018-05-28, issue #3095, fail on attempt to make hidden parent variable visible

data Nat : Set where
  suc : {n : Nat} → Nat

data IsSuc : Nat → Set where
  isSuc : ∀{n} → IsSuc (suc {n})

test : ∀{m} → IsSuc m → Set
test p = aux p
  where
  aux : ∀{n} → IsSuc n → Set
  aux isSuc = {!m!}  -- Split on m here

-- Context:
-- p  : IsSuc m
-- m : Nat  (out of scope)
-- n : Nat  (out of scope)

-- Expected error:
-- Cannot split on module parameter m
-- when checking that the expression ? has type Set
