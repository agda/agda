module Issue396 where

record ⊤ : Set where
  constructor tt

foo : (P : ⊤ → Set) →
      ((x : ⊤) → P x → P x) →
      (x y : ⊤) → P x → P y
foo P hyp x y = hyp x

-- Error was:
-- x != y of type ⊤
-- when checking that the expression hyp x has type P x → P y
