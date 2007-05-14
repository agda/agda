-- | Generates data used for precise syntax highlighting.

module Interaction.Highlighting.Generate
  ( generateSyntaxInfo
  , tests
  ) where

import Interaction.Highlighting.Precise hiding (tests)
import Syntax.Abstract
import Syntax.Translation.ConcreteToAbstract
import Data.Monoid

-- | Generates syntax highlighting information from a 'TopLevelInfo'.
--
-- Currently this is just a stub.

generateSyntaxInfo :: TopLevelInfo -> File
generateSyntaxInfo _ = return mempty

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO ()
tests = do
  return ()
