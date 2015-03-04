postulate
  F    : (Set → Set) → Set
  !_   : Set → Set
  !_,_ : Set → Set → Set
  X    : Set

syntax F (λ X → A) = X , A

infix 1 F
infix 2 !_

Foo : Set
Foo = ! X , X

-- This expression can be parsed in exactly one way. However, Agda
-- rejects it:
--
--   Expected variable name in binding position
--
-- The error is thrown from pure code in rebuildBinding, and this
-- action circumvents the parser logic.
--
-- The error was introduced in the fix for Issue 1129, and the problem
-- raised in Issue 1129 was introduced in a fix for Issue 1108
-- ("Operator parser performance").
