-- Andreas, 2017-01-08
-- Error range when "The name of the top level module does not match" to big

{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --type-in-type #-}

-- {-# OPTIONS -v scope.checkModuleName:100 #-}

module ThisIsTheWrongName where

postulate Something : Set

-- WAS: Error range included option pragmas.

-- Expected range: only the module name
