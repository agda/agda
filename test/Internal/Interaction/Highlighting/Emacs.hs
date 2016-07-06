
module Internal.Interaction.Highlighting.Emacs ( tests ) where

import Internal.TestHelpers

------------------------------------------------------------------------
-- All tests

-- TODO: One could check that the show functions are invertible.

-- | All the properties.

tests :: IO Bool
tests = runTests "Internal.Interaction.Highlighting.Emacs" []
