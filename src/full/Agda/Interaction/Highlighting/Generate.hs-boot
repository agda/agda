module Agda.Interaction.Highlighting.Generate where
import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Position (Range)

highlightAsTypeChecked
  :: (MonadTCM tcm, ReadTCState tcm)
  => Range
  -> Range
  -> tcm a
  -> tcm a
