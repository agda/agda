
module Issue277 where

data D : Set where
  d : D

abstract

  x : D
  x = d

-- Normalise x using the Emacs mode, at the top-level. Result: d. The
-- result should be x. Agda.Interaction.GhciTop.cmd_compute_toplevel
-- receives the right arguments, so the problem does not lie in the
-- Emacs Lisp code.

y : D
y = {!x!}  -- Normalisation works correctly in the goal.
