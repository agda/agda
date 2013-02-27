-- Andreas, 2013-02-27
module Issue653 where

postulate
  P : {A : Set} → (A → Set) → Set

mutual

  A : Set
  A = P B -- note A = P {A} B is non-terminating

  data B : A → Set where
    c : (a : A) → B a
-- This caused a stack overflow due to infinite reduction
-- in the positivity checker.
-- Now functions that do not pass the termination checker are not unfolded
-- any more.
-- So, it should report positivity violation now.
