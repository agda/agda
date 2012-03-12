-- Run this test case in safe mode
-- {-# OPTIONS --safe #-} -- does not parse (2012-03-12 Andreas)
module Issue586 where

{-# NO_TERMINATION_CHECK #-}
Foo : Set
Foo = Foo
