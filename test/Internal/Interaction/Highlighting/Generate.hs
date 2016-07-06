
module Internal.Interaction.Highlighting.Generate ( tests ) where

import Internal.TestHelpers

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Internal.Interaction.Highlighting.Generate" []
