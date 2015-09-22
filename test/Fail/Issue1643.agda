-- Andreas, 2015-09-09 Issue 1643
-- {-# OPTIONS -v tc.mod.apply:20 #-}
-- {-# OPTIONS -v scope:50 -v scope.inverse:100 -v interactive.meta:20 #-}

module _ where

module M where
  postulate A : Set

module N = M  -- This alias used to introduce a display form M.A --> N.A

open M

postulate
  a : A

test : Set
test = a

-- Error WAS: N.A !=< Set of type Set
-- SHOULD BE:   A !=< Set of type Set

{-
ScopeInfo
  current = ModuleAlias
  context = TopCtx
  modules
    scope
    scope ModuleAlias
      private
        names
          A --> [ModuleAlias.M.A]
      public
        modules
          M --> [ModuleAlias.M]
          N --> [ModuleAlias.N]
    scope ModuleAlias.M
      public
        names
          A --> [ModuleAlias.M.A]
    scope ModuleAlias.N
      public
        names
          A --> [ModuleAlias.N.A]
-}
