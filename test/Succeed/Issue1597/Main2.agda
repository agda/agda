-- Andreas, Jesper, 2015-07-02 Error in copyScope

{-# OPTIONS -v tc.decl:5 #-} -- KEEP, this forced Agda to look at A.Decls and loop

-- To trigger the bug, it is important that
-- the main module is in a subdirectory of the imported module.
module Issue1597.Main2 where

open import Issue1597   -- external import is needed

module B where
  open A public  -- public is needed

module C = B
  -- hanged when trying to print the Syntax.Abstract.Declarations
