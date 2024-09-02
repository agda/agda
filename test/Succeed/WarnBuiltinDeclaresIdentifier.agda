{-# OPTIONS --sized-types #-}

-- Andreas, 2024-08-15, trigger warning about qualified identifier

{-# BUILTIN SIZE Size.Type #-} -- deadcode

-- Pragma BUILTIN SIZE: expected unqualified identifier, but found Size.Type

-- Andreas, 2024-02-15, trigger warning BuiltinDeclaresIdentifier

{-# BUILTIN SIZEUNIV SizeUniv #-}
{-# BUILTIN SIZE     Size     #-}

postulate
  ∞ : Size

{-# BUILTIN SIZEINF  ∞        #-}

-- Expected warning:

-- BUILTIN SIZEINF declares an identifier (no longer expects an already defined identifier)
-- when scope checking the declaration
--   {-# BUILTIN SIZEINF ∞ #-}
