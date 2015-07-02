-- Andreas, Jesper, 2015-07-02 Error in copyScope

-- To trigger the bug, it is important that
-- the main module is in a subdirectory of the imported module.
module Issue1597.Main where

open import Issue1597   -- external import is needed

module B where
  open A public  -- public is needed

module C = B

postulate p : C.M.Nat

-- ERROR WAS: not in scope C.M.Nat
