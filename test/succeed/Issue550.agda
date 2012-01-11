module Issue550 where

data Box (A : Set) : Set where
  [_] : A → Box A

postulate
  A : Set
  B : Set
  b : B
  f : B -> A

⋯ : {{a : A}} → A
⋯ {{a = a}} = a

test : Box A
test =
  let a : A
      a = f b
  in [ ⋯ ]

-- should succeed.  Old message:
-- No variable of type A was found in scope.
-- when checking that the expression ⋯ has type A
