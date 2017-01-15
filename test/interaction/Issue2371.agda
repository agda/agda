-- Andreas, 2016-12-31, issue #2371 reported by subttle

-- Module parameter Nat shadowed by import
module Issue2371 (Nat : Set) where

open import Agda.Builtin.Nat

-- C-c C-n zero RET

-- ERROR WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Utils/List.hs:304

-- Should succeed.

-- C-c C-n Nat RET will report an ambiguous name
