module Issue734a where

module M₁ (Z : Set₁) where

  postulate
    P : Set
    Q : Set → Set

module M₂ (X Y : Set) where

  module M₁′ = M₁ Set
  open M₁′

  p : P
  p = {!!}

  -- Previous and current agda2-goal-and-context:

  -- Y : Set
  -- X : Set
  -- ---------
  -- Goal: P

  q : Q X
  q = {!!}

  -- Previous and current agda2-goal-and-context:

  -- Y : Set
  -- X : Set
  -- -----------
  -- Goal: Q X

postulate X : Set

pp : M₂.M₁′.P X X
pp = {!!}

  -- Previous agda2-goal-and-context:

  -- ----------------
  -- Goal: M₁.P Set

  -- Current agda2-goal-and-context:

  -- --------------------
  -- Goal: M₂.M₁′.P X X
