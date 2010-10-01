-- 2010-10-01 Issue 342
module NonDependentConstructorType where

data Wrap : Set1 where
  wrap : Set -> Wrap

bla : Set
bla = wrap
-- 2010-10-01 error is printed as (_ : Set) -> Wrap !=< Set
-- error should be printed as Set -> Wrap !=< Set