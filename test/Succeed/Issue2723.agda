-- Andreas, 2017-08-28, issue #2723, reported by Andrea

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS --warning=error #-}
-- {-# OPTIONS -v tc.cover:30 #-}

record Test : Set1 where
  field
    one two : Set
open Test

foo : Test
foo .one = {!!}
foo = {!!}
foo .two = {!!}

-- WAS: internal error in clause compiler

-- NOW: warning about unreachable clause
