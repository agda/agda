-- | Generates data used for precise syntax highlighting.

module Interaction.Highlighting.Generate
  ( generateSyntaxInfo
  , tests
  ) where

import Interaction.Highlighting.Precise hiding (tests)
import Syntax.Abstract
import Syntax.Translation.ConcreteToAbstract

-- | Generates syntax highlighting information from a 'TopLevelInfo'.
--
-- Currently this is just a stub.

generateSyntaxInfo :: TopLevelInfo -> File
generateSyntaxInfo _ = File []

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO ()
tests = do
  return ()
