-- Andreas, 2026-10-20, issue #8835
-- A CannotEliminateWithPattern confused me because it mentions a type
-- and a pattern that fits the type.
-- However, "eliminate" is not "match", it means that we can apply
-- a value of the given type to the pattern.

variable
  A B : Set

data ⊥ : Set where

infixr 10 ¬_

¬_ : Set → Set
¬ A = A → ⊥

infixl 8 _∨_

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

test : ¬ ¬ (A ∨ ¬ A)
test k = k λ where
  (inl a)  → ?
  (inr na) → ?

-- error WAS: [CannotEliminateWithPattern]
-- Cannot eliminate type (A ∨ ¬ A) with constructor pattern (inl a)
-- (did you supply too many arguments?)
-- when checking the clause left hand side
-- .extendedlambda0 (inl a)

-- New error adds "it is not a function type" to the parenthesis.
