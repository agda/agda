-- Andreas, 2024-07-21, PR #7379
-- Trigger error VariableIsOfUnusableCohesion

{-# OPTIONS --cohesion #-}

postulate
  test : {A : Set} (@♭ x : A) → A

-- Expected error:
-- Variable A is declared Squash so it cannot be used here
