-- Andreas, 2019-10-21, issue #4148, reported by omelkonian

{-# OPTIONS -v impossible:100 #-}

postulate
  A : Set

module M (I : Set) where

  postulate
    P : I → Set

  record R (i : I) : Set where
    constructor mk
    field
      f : P i

open module N = M A

data D : ∀ {i} → R i → Set where
  c : ∀ {i} {t : P i} → D (mk t)

test : ∀ {i} {t : R i} → D t → Set₁
test c = Set

-- WAS: internal error in a sanity check in etaExpandRecord'_

-- Should succeed
