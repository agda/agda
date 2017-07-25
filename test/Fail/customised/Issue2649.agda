-- Andreas, 2017-07-25, issue #2649, reported by gallais
-- Serialization killed range needed for error message.

-- {-# OPTIONS -v scope.clash:60 #-}

module Issue2649 where

open import Issue2649-1
open import Issue2649-2

id : (A : Set) → A → A
id A x = M.foo
  where
  module M = MyModule A x

-- Expected:
-- Duplicate definition of module M. Previous definition of module M
-- at .../Issue2649-2.agda:5,13-14
