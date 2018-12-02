-- Jesper, 2018-12-02, Issue #1063: Since we freeze metavariables
-- after each declaration, it only makes sense to also freeze metas
-- *before* the first declaration in a module.

module _ where

module M (A : _) where

  x : Set
  x = A
