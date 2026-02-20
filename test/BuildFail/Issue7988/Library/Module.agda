-- Andreas, 2026-02-19, issue #7988, reported by Felix Cherubini

-- The following declaration is not allowed before the top-level module declaration.
variable
  A : Set

module Library.Module where

-- error WAS: [ModuleNameDoesntMatchFileName]
-- The inferred name `Module` of the top level module does not match the file name.
-- A such named module should be defined in one of the following files: ...
-- (Hint: no module header was found in this file; adding one might fix this error.)

-- Expected error: [IllegalDeclarationBeforeTopLevelModule]
-- Illegal declaration(s) before top-level module
