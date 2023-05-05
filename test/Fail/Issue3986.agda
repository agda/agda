-- Andreas, 2022-10-28, issue #3986
-- This issue has been fixed by the removal for subtyping
-- (in particular, subtyping for irrelevant function types).

{-# OPTIONS --subtyping #-}

postulate
  A   : Set
  a b : A
  f   : .A → A
  P   : A → Set
  p   : ∀ x → P x

app : (A → A) → A
app f = f a

test-failing : P (app f)
test-failing with b
... | _ = p (f a)


-- A ≤ .A
-- .A → B ≤ A → B

-- app f a --> f a
