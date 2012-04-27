module Agda.Interaction.Highlighting.Generate where
import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Position (Range)

highlightAsTypeChecked
  :: (MonadTCM tcm)
  => tcm a
  -> Range
  -> Range
  -> tcm a
