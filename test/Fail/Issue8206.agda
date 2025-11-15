-- Andreas, 2025-11-15, issue #8206
-- "interleaved mutual" did not catch disallowed parts
-- of parameters in data/record definition.

interleaved mutual

  data _≡_ {A : Set} (a : A) : A → Set where
  data Nat : Set where
  data IsZero (n : Set) : Set

  data _≡_ A a where
    refl : a ≡ a

  data Nat where
    zero : Nat

  data IsZero (n : Nat) where
    zero : n ≡ zero → IsZero n

  data Nat where
    suc : Nat → Nat

-- warning: -W[no]InvalidDataOrRecDefParameter
-- Ignoring misplaced type of parameter in a data definition

-- error: [UnequalSorts]
-- Set₁ != Set
-- when checking that the solution Set of metavariable _A_11 has the
-- expected type Set
