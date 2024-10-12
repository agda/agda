-- Andreas, 2024-10-12, trigger error Syntax.BadMacroDef

macro
  data Empty : Set

-- error: [Syntax.BadMacroDef]
-- Data types are not allowed in macro blocks
