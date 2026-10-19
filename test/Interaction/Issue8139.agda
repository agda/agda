-- Andreas, 2025-10-25, issue #8139
-- Allow copattern-catchalls for the sake of splitting.

-- {-# OPTIONS -v interaction.case.filter:20 #-}
-- {-# OPTIONS -v tc.cover:30 #-}

open import Agda.Builtin.Sigma

postulate
  A : Set
  B : A → Set
  a : A
  b : B a

test : Σ A B
test .fst = a
test = {!!}  -- C-c C-c RET
