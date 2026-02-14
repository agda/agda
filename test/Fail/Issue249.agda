
module Issue249 where

postulate
  A B : Set

module A where
  X = A;  X' = A
  Y = B;  Y' = B
  module M where
  module N where

open A renaming (X  to C; Y  to C)
       renaming (X' to D; Y' to D)
       renaming (module M to ,; module N to ,)

-- Expected error: [DuplicateImports]
-- Ambiguous imports from module A for identifiers: module ,; C; D
-- when scope checking the declaration
--   open A renaming (X to C; Y to C; X' to D; Y' to D; module M to ,;
--                    module N to ,)
