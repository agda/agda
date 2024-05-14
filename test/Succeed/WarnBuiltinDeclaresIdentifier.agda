-- Andreas, 2024-02-15, trigger warning BuiltinDeclaresIdentifier

{-# OPTIONS --sized-types #-}

{-# BUILTIN SIZEUNIV SizeUniv #-}
{-# BUILTIN SIZE     Size     #-}

postulate
  ∞ : Size

{-# BUILTIN SIZEINF  ∞        #-}

-- Expected warning:

-- BUILTIN SIZEINF declares an identifier (no longer expects an already defined identifier)
-- when scope checking the declaration
--   {-# BUILTIN SIZEINF ∞ #-}
