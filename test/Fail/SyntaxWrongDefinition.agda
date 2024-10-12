-- Andreas, 2024-10-12, trigger error Syntax.WrongDefinition

record R : Set
data R where

-- error: [Syntax.WrongDefinition]
-- R has been declared as a record type, but is being defined as a data type
