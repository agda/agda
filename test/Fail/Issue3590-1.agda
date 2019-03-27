-- The debug output should include the text "Termination checking
-- mutual block MutId 0" once, not three times.

{-# OPTIONS -vterm.mutual.id:40 #-}

record R : Set₁ where
  constructor c
  field
    A : Set

  _ : A → A
  _ = λ x → x

  _ : A → A
  _ = λ x → x

  _ : A → A
  _ = λ x → x

-- Included in order to make the code fail to type-check.

Bad : Set
Bad = Set
