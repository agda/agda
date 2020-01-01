-- Andreas, 2018-05-28, issue #3095, cannot make hidden shadowing variable visible
-- Andreas, 2019-07-15, issue #3919, make hidden variable visible in par. module

open import Agda.Builtin.Equality

module _ (A : Set) where

data Nat : Set where
  suc : {n : Nat} → Nat

data IsSuc : Nat → Set where
  isSuc : ∀{n} → IsSuc (suc {n})

test₁ : ∀{n} → IsSuc n → Set
test₁ p = aux p
  where
  aux : ∀{n} → IsSuc n → Set
  aux isSuc = {!n₁!}  -- C-c C-c
  -- Expected: aux (isSuc {n}) = {!!}

-- Context:
-- p  : IsSuc n
-- n : Nat  (not in scope)
-- n₁ : Nat  (not in scope)

-- WAS: ERROR
-- Ambiguous variable n
-- when checking that the expression ? has type Set

test₂ : ∀{m} → IsSuc m → Set
test₂ p = aux p
  where
  aux : ∀{n} → IsSuc n → Set
  aux isSuc = {!m!} -- C-c C-c
  -- Expected: cannot make hidden module parameter m visible

test₃ : ∀ m → IsSuc m → Set
test₃ m p = aux p refl
  where
  aux : ∀{n} → IsSuc n → m ≡ n → Set
  aux isSuc refl = {!n!} -- C-c C-c
  -- Expected: aux (isSuc {n}) refl = ?

test₄ : Nat → Nat
test₄ x = bar x
  where
    bar : Nat → Nat
    bar y = {!x!} -- C-c C-c
    -- Expected: cannot split on module parameter x

test₅ : Nat → {n : Nat} → Nat → Nat
test₅ = λ x y → {!n!} -- C-c C-c
    -- Expected: cannot make hidden lambda-bound variable n visible

issue3919 : {n m : Nat} → n ≡ m
issue3919 = {!m!} -- C-c C-c
    -- Expected: issue3919 {m = m} = ?
