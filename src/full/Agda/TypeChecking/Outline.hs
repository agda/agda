module Agda.TypeChecking.Outline where

import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Base

import Agda.Interaction.Options.Lenses
import Agda.Interaction.Options.Base

import Control.Monad

import qualified Agda.Interaction.Highlighting.Range as Range
import qualified Agda.Utils.RangeMap as RangeMap
import Agda.Utils.Lens

import Data.Monoid (Last(..))

import Agda.Syntax.Position
import Agda.Syntax.Internal

-- | Record that the given range has the given type in the outline.
-- Automatically includes the context.
recordTypeInContext
  :: ( HasOptions m
     , MonadTCState m
     , MonadTCEnv m
     )
  => Range -> Type
  -> m ()
recordTypeInContext range ty = do
  opt <- getCommandLineOptions <$> getTC
  when (optPositionalTypes opt) $ do
    ctx <- reverse <$> getContext
    modifyTCLens' stOutline $ \s -> RangeMap.insert mappend
      (Range.rangeToRange range)
      (Last (Just (TypeInContext ctx ty)))
      s
