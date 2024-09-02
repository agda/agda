-- Issue #2324
-- Prevent 'with' on a module parameter through the backdoor.

Type-of : {A : Set} → A → Set
Type-of {A = A} _ = A

module _ (A : Set) where

  Foo : A → Set
  Foo a with Type-of a
  ... | B = B

-- Should fail.  Expected error:
--
-- Cannot 'with' on expression Type-of a which reduces to variable A
-- bound in a module telescope (or patterns of a parent clause)
-- when inferring the type of Type-of a
