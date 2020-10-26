-- making sure that the fun clauses are kept in declaration order
-- in an interleaved mutual block

open import Agda.Builtin.Nat

interleaved mutual

  plus  : Nat → Nat → Nat
  minus : Nat → Nat → Nat

  -- 0 being neutral
  plus 0 n = n
  minus n 0 = n

  -- other 0 case
  plus n 0 = n
  minus 0 n = 0

  -- suc suc
  plus (suc m) (suc n) = suc (suc (plus m n))
  minus (suc m) (suc n) = minus m n

-- All of these test cases should be true by computation
-- It will not be the case if the definitions have been interleaved
-- the wrong way around (because the resulting definition would be
-- strict in a different argument)

open import Agda.Builtin.Equality

_ : ∀ {n} → plus 0 n ≡ n
_ = refl

_ : ∀ {n} → minus n 0 ≡ n
_ = refl

-- The following should not check with refl; for the same reasons

-- _ : ∀ {n} → plus n 0 ≡ n
-- _ = refl

-- _ : ∀ {n} → minus 0 n ≡ 0
-- _ = refl

-- but they are of course provable by case analysis:

_ : ∀ n → plus n 0 ≡ n
_ = λ where
      zero → refl
      (suc _) → refl

_ : ∀ n → minus 0 n ≡ 0
_ = λ where
      zero → refl
      (suc _) → refl
