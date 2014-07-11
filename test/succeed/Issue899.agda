-- Andreas, 2013-11-07
-- Instance candidates are now considered module judgemental equality.
module Issue899 where

postulate
  A B : Set
  f : {{ x : A }} → B
  instance a : A

instance
  a' : A
  a' = a

test : B
test = f

{- The previous code fails with the following message:

  Resolve implicit argument _x_257 : A. Candidates: [a : A, a : A]

There are indeed two values in scope of type A (a and a'), but given
that they are definitionally equal, Agda should not complain about it
but just pick any one of them.  -}
