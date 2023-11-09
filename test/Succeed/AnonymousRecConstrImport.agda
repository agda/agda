module AnonymousRecConstrImport where

open import AnonymousRecConstr

-- Tests that Record.constructor syntax works across imports.

_ = Bar.constructor
