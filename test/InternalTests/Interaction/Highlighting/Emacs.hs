
module InternalTests.Interaction.Highlighting.Emacs ( tests ) where

import InternalTests.Helpers

------------------------------------------------------------------------
-- All tests

-- TODO: One could check that the show functions are invertible.

-- | All the properties.

tests :: IO Bool
tests = runTests "InternalTests.Interaction.Highlighting.Emacs" []
