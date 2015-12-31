-- ASR (31 December 2015). The error message for this test was changed
-- by fixing Issue 1763.

module Issue586 where

{-# NO_TERMINATION_CHECK #-}
Foo : Set
Foo = Foo
