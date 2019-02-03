-- Andreas, 2019-02-03, issue #3541:
-- Treat indices like parameters in positivity check.

data Works (A : Set) : Set where
  nest : Works (Works A) → Works A

data Foo : Set → Set where
  foo : ∀{A} → Foo (Foo A) → Foo A

-- Should pass.
