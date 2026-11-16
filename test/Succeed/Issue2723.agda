-- Andreas, 2017-08-28, issue #2723, reported by Andrea

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS --warning=error #-}
-- {-# OPTIONS -v tc.cover:30 #-}

record Test (A : Set) : Set where
  field
    one two : A
open Test

foo : {A : Set} → Test A
foo .one = {!!}
foo = {!!}
foo .two = {!!}

-- WAS: internal error in clause compiler

-- THEN: warning about unreachable clause

-- NOW: error:
-- Cannot split into projections because not all clauses have a
-- projection copattern
-- when checking the definition of foo

-- Andreas, 2025-10-24, issue #8139, back to
-- warning: -W[no]UnreachableClauses
-- Unreachable clause
-- when checking the definition of foo
