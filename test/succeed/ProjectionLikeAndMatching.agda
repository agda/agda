module ProjectionLikeAndMatching where

data Unit : Set where
  * : Unit

data Box A : Set where
  [_] : A → Box A

-- Unbox should not be considered projection-like since it's matching on more than
-- the eliminatee.
unbox : ∀ {A} → Box A → Unit → A
unbox [ x ] * = x

postulate
  Thm : {A : Set} → A → Set
  prf : {A : Set}(x : A) → Thm x

-- If unbox was projection-like we would end up with
--   [_] (apply x) (elim unbox) (apply u) : A
-- and we wouldn't be able to reconstruct the parameter
-- argument to [_].
lem : ∀ {A} (x : A) u → Thm (unbox [ x ] u)
lem x u = prf (unbox [ x ] u)
