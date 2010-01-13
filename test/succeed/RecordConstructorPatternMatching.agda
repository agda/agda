-- Record constructors are not allowed in patterns.

module RecordConstructorPatternMatching where

record R : Set₁ where
  constructor con
  field
    {A}         : Set
    f           : A → A
    {B C} D {E} : Set
    g           : B → C → E

id : R → R
id (con f D g) = con f D g
