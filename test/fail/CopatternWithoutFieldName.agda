-- 2011-11-24 Andreas, James
{-# OPTIONS --copatterns #-}
module CopatternWithoutFieldName where

record R : Set2 where
  field
    f : Set1
open R

test : (f : R -> Set1) -> R
test f = bla where
  bla : R
  f bla = Set
-- not a copattern, since f not a field name

