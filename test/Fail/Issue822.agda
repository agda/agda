-- {-# OPTIONS -v tc.lhs:40 #-} {-# OPTIONS -v scope.pat:40 #-}
module Issue822 where

module M₁ where

  postulate [_] : Set

module M₂ where

  data D : Set₁ where
    [_] : Set → D

module M₃ where

  data D : Set₁ where
    [_] : Set → D

open M₁
open M₂
open M₃

Foo : _ → Set
Foo [ A ] = A

-- Strange error message:

-- Bug.agda:16,1-14
-- Left hand side gives too many arguments to a function of type
-- D → Set
-- when checking that the clause Foo [ A ] = A has type D → Set

-- If the two open statements are swapped, then we get a more
-- reasonable error message:

-- Bug.agda:16,1-10
-- Ambiguous name [_]. It could refer to any one of
--   M₂.[_] bound at [...]/Bug.agda:10,5-8
--   M₁.[_] bound at [...]/Bug.agda:5,13-16
-- when scope checking the left-hand side Foo [ A ] in the definition
-- of Foo

-- One could perhaps also argue that the code above should be
-- syntactically correct, because M₁.[_] can't be used in the pattern
-- (except for under a dot).

-- Andreas, 2013-03-21
-- To reproduce an error, one now needs ambiguous constructors.
