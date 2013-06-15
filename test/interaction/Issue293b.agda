module Issue293b where

module M₁ (_ : Set₁) where

  postulate P : Set

module M₂ (_ : Set) where

  open M₁ Set

  p : P
  p = {!!}

  -- Previous agda2-goal-and-context:

  -- ------------------------
  -- Goal: M₁.P Set

  -- Current agda2-goal-and-context:

  -- ------------------------
  -- Goal: P
