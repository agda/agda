-- Andreas, 2012-06-07
-- {-# OPTIONS --show-implicit -v tc.rec:100 -v tc.meta.assign:15 #-}
module Issue387 where

import Common.Level

mutual

  record R' (A : Set) : Set where
    field f : _

  c' : {A : Set} -> A -> R' A
  c' a = record { f = a }

-- previous to fix of 387, this had an unresolved meta
-- because two metas were created for _
