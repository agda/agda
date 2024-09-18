
module Agda.TypeChecking.Warnings
  ( MonadWarning(..)
  , warning'_, warning_, warning', warning, warnings
  , raiseWarningsOnUsage
  , isUnsolvedWarning
  , isMetaWarning
  , isMetaTCWarning
  , onlyShowIfUnsolved
  , WhichWarnings(..), classifyWarning
  -- not exporting constructor of WarningsAndNonFatalErrors
  , WarningsAndNonFatalErrors, tcWarnings, nonFatalErrors
  , classifyWarnings
  ) where

import Control.Monad ( forM, unless )
import Control.Monad.Except ( MonadError(..) )
import Control.Monad.Reader ( ReaderT )
import Control.Monad.State  ( StateT )
import Control.Monad.Trans  ( MonadTrans, lift )
import Control.Monad.Trans.Maybe
import Control.Monad.Writer ( WriterT )

import Data.Foldable
import qualified Data.List as List
import qualified Data.Map  as Map
import qualified Data.Set  as Set
import Data.Maybe     ( catMaybes )
import Data.Semigroup ( Semigroup, (<>) )

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Caching
import {-# SOURCE #-} Agda.TypeChecking.Pretty ( MonadPretty, prettyTCM, vcat, ($$) )
import {-# SOURCE #-} Agda.TypeChecking.Pretty.Call
import {-# SOURCE #-} Agda.TypeChecking.Pretty.Warning ( prettyWarning )

import Agda.Syntax.Abstract.Name ( QName )
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Position
import Agda.Syntax.Parser

import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings
import {-# SOURCE #-} Agda.Interaction.Highlighting.Generate (highlightWarning)

import Agda.Utils.CallStack ( CallStack, HasCallStack, withCallerCallStack )
import Agda.Utils.Function  ( applyUnless )
import Agda.Utils.Lens
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import qualified Agda.Utils.Set1 as Set1
import Agda.Utils.Singleton

import Agda.Utils.Impossible


-- * The warning monad
---------------------------------------------------------------------------

class (MonadPretty m, MonadError TCErr m) => MonadWarning m where
  -- | Store a warning and generate highlighting from it.
  addWarning :: TCWarning -> m ()

  default addWarning
    :: (MonadWarning n, MonadTrans t, t n ~ m)
    => TCWarning -> m ()
  addWarning = lift . addWarning

instance MonadWarning m => MonadWarning (MaybeT m)
instance MonadWarning m => MonadWarning (ReaderT r m)
instance MonadWarning m => MonadWarning (StateT s m)
instance (MonadWarning m, Monoid w) => MonadWarning (WriterT w m)

instance MonadWarning TCM where
  addWarning tcwarn = do
    stTCWarnings `modifyTCLens` Set.insert tcwarn
    highlightWarning tcwarn

-- * Raising warnings
---------------------------------------------------------------------------

{-# SPECIALIZE warning'_ :: CallStack -> Warning -> TCM TCWarning #-}
warning'_ :: (MonadWarning m) => CallStack -> Warning -> m TCWarning
warning'_ loc w = do
  r <- viewTC eRange
  c <- viewTC eCall
  b <- areWeCaching
  let r' = case w of
        -- Some warnings come with their own error locations.
        NicifierIssue             w0 -> getRange w0
        UnsolvedInteractionMetas  rs -> getRange rs
        UnsolvedMetaVariables     rs -> getRange rs
        UnsolvedConstraints       cs -> getRange cs
        InteractionMetaBoundaries rs -> getRange rs
        _ -> r
  let wn = warningName w
  let ws = warningName2String wn
  p <- vcat
    [ pure $ P.hsep
      [ if null r' then mempty else P.pretty r' P.<> P.colon
      , if wn `elem` errorWarnings then "error:" P.<+> P.brackets (P.text ws)
        else P.text $ "warning: -W[no]" ++ ws
        -- Only benign warnings can be deactivated with -WnoXXX.
      ]
    , prettyWarning w
    , prettyTCM c
    ]
  return $ TCWarning loc r' w p (P.render p) b

{-# SPECIALIZE warning_ :: Warning -> TCM TCWarning #-}
warning_ :: (HasCallStack, MonadWarning m) => Warning -> m TCWarning
warning_ = withCallerCallStack . flip warning'_

-- UNUSED Liang-Ting Chen 2019-07-16
---- | @applyWarningMode@ filters out the warnings the user has not requested
---- Users are not allowed to ignore non-fatal errors.
--
--applyWarningMode :: WarningMode -> Warning -> Maybe Warning
--applyWarningMode wm w = case classifyWarning w of
--  ErrorWarnings -> Just w
--  AllWarnings   -> w <$ guard (Set.member (warningName w) $ wm ^. warningSet)

{-# SPECIALIZE warnings' :: CallStack -> List1 Warning -> TCM () #-}
warnings' :: MonadWarning m => CallStack -> List1 Warning -> m ()
warnings' loc ws = do

  wmode <- optWarningMode <$> pragmaOptions

  -- We collect *all* of the warnings no matter whether they are in the @warningSet@
  -- or not. If we find one which should be turned into an error, we keep processing
  -- the rest of the warnings and *then* report all of the errors at once.
  merrs <- forM ws $ \ w' -> do
    tcwarn <- warning'_ loc w'
    if wmode ^. warn2Error && warningName w' `elem` wmode ^. warningSet
    then pure (Just tcwarn)
    else Nothing <$ addWarning tcwarn

  List1.unlessNull (List1.catMaybes merrs) \ errs ->
    typeError' loc $ NonFatalErrors $ Set1.fromList errs

{-# SPECIALIZE warnings :: HasCallStack => List1 Warning -> TCM () #-}
warnings :: (HasCallStack, MonadWarning m) => List1 Warning -> m ()
warnings = withCallerCallStack . flip warnings'

{-# SPECIALIZE warning' :: CallStack -> Warning -> TCM () #-}
warning' :: MonadWarning m => CallStack -> Warning -> m ()
warning' loc = warnings' loc . singleton

{-# SPECIALIZE warning :: HasCallStack => Warning -> TCM () #-}
warning :: (HasCallStack, MonadWarning m) => Warning -> m ()
warning = withCallerCallStack . flip warning'

-- | Raise every 'WARNING_ON_USAGE' connected to a name.
{-# SPECIALIZE raiseWarningsOnUsage :: QName -> TCM () #-}
raiseWarningsOnUsage :: (MonadWarning m, ReadTCState m) => QName -> m ()
raiseWarningsOnUsage d = do
  -- In case we find a defined name, we start by checking whether there's
  -- a warning attached to it
  reportSLn "scope.warning.usage" 50 $ "Checking usage of " ++ P.prettyShow d
  mapM_ (warning . UserWarning) =<< Map.lookup d <$> getUserWarnings


-- * Classifying warnings
---------------------------------------------------------------------------

isUnsolvedWarning :: Warning -> Bool
isUnsolvedWarning w = warningName w `Set.member` unsolvedWarnings

isMetaWarning :: Warning -> Bool
isMetaWarning = \case
   UnsolvedInteractionMetas{} -> True
   UnsolvedMetaVariables{}    -> True
   _                          -> False

isMetaTCWarning :: TCWarning -> Bool
isMetaTCWarning = isMetaWarning . tcWarning

onlyShowIfUnsolved :: Warning -> Bool
onlyShowIfUnsolved InversionDepthReached{} = True
onlyShowIfUnsolved _ = False

-- | Classifying warnings: some are benign, others are (non-fatal) errors

data WhichWarnings =
    ErrorWarnings -- ^ warnings that will be turned into errors
  | AllWarnings   -- ^ all warnings, including errors and benign ones
  -- Note: order of constructors is important for the derived Ord instance
  deriving (Eq, Ord)

classifyWarning :: Warning -> WhichWarnings
classifyWarning w =
  if warningName w `Set.member` errorWarnings
  then ErrorWarnings
  else AllWarnings

classifyWarnings :: [TCWarning] -> WarningsAndNonFatalErrors
classifyWarnings ws =
    WarningsAndNonFatalErrors (Set.fromList warnings) (Set.fromList errors)
  where
    partite = (< AllWarnings) . classifyWarning . tcWarning
    (errors, warnings) = List.partition partite ws
