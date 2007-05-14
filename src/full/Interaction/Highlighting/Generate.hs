-- | Generates data used for precise syntax highlighting.

module Interaction.Highlighting.Generate
  ( generateSyntaxInfo
  , tests
  ) where

import Interaction.Highlighting.Precise hiding (tests)
import TypeChecking.Monad
import qualified Syntax.Abstract as A
import Syntax.Translation.ConcreteToAbstract
import Data.Monoid

-- | Generates syntax highlighting information from a 'TopLevelInfo'.
--
-- Currently this is just a stub.

-- TODO: Walk through all declarations.
-- * For every name encountered, look it up and determine which
--   aspects it satisfies.
-- * String and numeric literals and dotted patterns should also be
--   detected.
-- * Furthermore all keywords and comments should be marked, but this
--   may require a more concrete input.

generateSyntaxInfo :: TopLevelInfo -> TCM File
generateSyntaxInfo top = fmap mconcat $ mapM decl $ topLevelDecls top

decl :: A.Declaration -> TCM File
decl (A.Axiom defInfo qName expr) = return mempty
decl (A.Primitive defInfo qName expr) = return mempty
decl (A.Definition declInfo types defs) = return mempty
decl (A.Section moduleInfo moduleName typedBindingss decls) = return mempty
decl (A.Apply moduleInfo moduleName1 moduleName2 namedArgs qNameMap moduleNameMap) = return mempty
decl (A.Import moduleInfo moduleName) = return mempty
decl (A.Pragma range pragma) = return mempty
decl (A.ScopedDecl scopeInfo decls) = return mempty

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO ()
tests = do
  return ()
