-- Andreas, 2018-05-28, issue #3095, cannot make hidden shadowing variable visible

data Nat : Set where
  suc : {n : Nat} → Nat

data IsSuc : Nat → Set where
  isSuc : ∀{n} → IsSuc (suc {n})

test : ∀{n} → IsSuc n → Set
test p = aux p
  where
  aux : ∀{n} → IsSuc n → Set
  aux isSuc = {!.n!}  -- Split on .n here

-- Context:
-- p  : IsSuc .n
-- .n : Nat
-- .n : Nat

-- ERROR
-- Ambiguous variable .n
-- when checking that the expression ? has type Set
