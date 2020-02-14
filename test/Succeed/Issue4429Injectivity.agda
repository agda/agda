-- Andreas, 2020-02-10, issue 4429, reported by Nisse
--
-- Injectivity analysis can make type checker loop (or slow down)
-- since it reduces the rhs of definitions.
--
-- Try to be smarter and do not needlessly invoke the injectivity
-- analysis.  For instance, do not consider a projection pattern
-- a proper match for the sake of injectivity, since a metavariable
-- cannot occupy its position (unlike for constructor and literal patterns).

-- {-# OPTIONS -v tc.inj.check:45 #-}

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

postulate
  A : Set

{-# TERMINATING #-}

to : A → A
to = to  -- An approximation of slow but terminating code.

{-# TERMINATING #-}

from : A → A
from = from  -- An approximation of slow but terminating code.

works : A ⇔ A
works = record
  { to   = to
  ; from = from
  }

test : A ⇔ A
test ._⇔_.to   = to
test ._⇔_.from = from

-- WAS: Definition by copatterns loops, because the injectivity
-- checker tries to reduce the rhs.

-- Should pass, since now injectivity checker does not consider
-- a projection pattern as proper match.
-- Thus, injectivity for this function would be pointless.
