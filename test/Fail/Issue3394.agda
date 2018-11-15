-- Andreas, 2018-11-15, issue #3394 and testcase by Guillaume Brunerie
--
-- Internal error in termination checking the type of Ploop
-- due to uninitialized terSizeDepth.

postulate
  A : Set
  B : Set
  P : B → Set

mutual
  loop  : A → B → B
  loop a b = loop a b

  Ploop : (b : B) → P (loop _ b)  -- Unsolved meta caused internal error
  Ploop b = whatever
    where postulate whatever : _

-- Should fail termination checking in a controlled fashion.
