{-# OPTIONS --allow-unsolved-metas #-}

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

data D : Set where
  c : D → D

postulate
  d : D
  A : Set
  P : A → Set

record R : Set where
  no-eta-equality
  field
    f : A

  -- R : Set
  -- Rf : R → A

data Box : Set where
  box : R → Box

postulate
  f : D → Box

-- pat-lam : Box → A
-- pat-lam (box y) = R.f y

g : D → A
g x = case f x of λ
  { (box y) → R.f y
  }

postulate B : Set

p : P (g (c d))
p with B
p | z = {!!}
