-- Andreas, 2025-11-12, issue #8197, report and testcase by Oskar Eriksson
-- Order of meta-variables wrong after refining goal with an expression
-- that contains a `?`.
-- This occurred only when the hole was "too small" to fit the expression.

-- {-# OPTIONS -v interaction.give:30 #-}

postulate
  A B C : Set
  g : A → B
  f : B → B → C

foo : C
foo = {!!} -- C-c C-r "f (g ?)"
-- For the reproducer, it is important that the hole is empty upon load.
-- Also, it should not be wide enough to hold "f (g ?)".

-- WAS: Refining with "f (g ?)" produces:
--
-- (agda2-info-action "*All Goals*" "?1 : A ?2 : B" nil)
-- ((last . 1) . (agda2-goals-action '(2 1)))
--
-- Correct is:
--
-- ((last . 1) . (agda2-goals-action '(1 2)))
