-- Andreas, 2015-07-10, issue reported by asr
-- {-# OPTIONS -v scope:20 #-}
-- {-# OPTIONS -v scope.createModule:10 #-}
module _ where

module A where
  module Y where

module B where
  -- FAILS:
  module X = A
  open X public
  -- open A public  --WORKS

module C = B

-- On maint and master:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/Syntax/Scope/Monad.hs:107

{-
createModule Issue1607.C
module macro
ScopeInfo
  current = Issue1607
  context = TopCtx
  modules
    scope
    scope Issue1607
      public
        modules
          A --> [Issue1607.A]
          B --> [Issue1607.B]
    scope Issue1607.A
      public
        modules
          Y --> [Issue1607.A.Y]
    scope Issue1607.A.Y
    scope Issue1607.B
      public
        modules
          X --> [Issue1607.B.X]
          Y --> [Issue1607.B.X.Y]
    scope Issue1607.B.X
      public
        modules
          Y --> [Issue1607.B.X.Y]
    scope Issue1607.B.X.Y
    scope Issue1607.C

Copying scope Issue1607.B to Issue1607.C
createModule Issue1607.C.X
Copying scope Issue1607.B.X to Issue1607.C.X
createModule Issue1607.C.X.Y
Copying scope Issue1607.B.X.Y to Issue1607.C.X.Y
createModule Issue1607.C.X.Y
Copying scope Issue1607.B.X.Y to Issue1607.C.X.Y
-}
