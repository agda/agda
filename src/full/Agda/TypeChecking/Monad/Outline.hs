module Agda.TypeChecking.Monad.Outline where

import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Imports
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Reduce

import {-# SOURCE #-} Agda.TypeChecking.Pretty

import qualified Agda.Interaction.Highlighting.Range as Range
import qualified Agda.Utils.RangeMap as RangeMap
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Impossible
import Agda.Utils.FileName
import Agda.Utils.Lens

import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Common

import Control.Monad.IO.Class
import Control.DeepSeq
import Control.Monad

import qualified Data.ByteString.Lazy as Bsl
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.Vector as Vector
import qualified Data.Text as Text
import Data.Foldable
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Monoid (Last(..))
import Data.Maybe
import Data.Aeson
import Data.Text (Text)

import GHC.Generics

import System.IO


data OutlinePending
  = OutlinePending
    { outlineRange   :: {-# UNPACK #-} !Range.Range
    , outlineContext :: Context
    , outlineScope   :: {-# UNPACK #-} !ScopeInfo
    , outlineType    :: {-# UNPACK #-} !Type
    }

data OutlineGlobal
  = OutlineGlobal
    { globalNameId :: {-# UNPACK #-} !NameId
    , globalStart  :: {-# UNPACK #-} !Int
    , globalEnd    :: {-# UNPACK #-} !Int
    , globalMod    :: {-# UNPACK #-} !TopLevelModuleName
    , globalType   :: {-# UNPACK #-} !Text
    }
  deriving (Eq, Show, Generic)

data OutlineEntry
  = OutlineEntry
    { entryStart    :: {-# UNPACK #-} !Int
    , entryEnd      :: {-# UNPACK #-} !Int
    , entryMod      :: {-# UNPACK #-} !TopLevelModuleName
    , entryContext  :: HashMap.HashMap Text Text
    , entryRelevant :: HashMap.HashMap Text OutlineGlobal
    , entryType     :: {-# UNPACK #-} !Text
    }
  deriving (Eq, Show, Generic)

instance NFData OutlineEntry
instance NFData OutlineGlobal

instance ToJSON OutlineGlobal
instance ToJSON OutlineEntry

data OutlineOutputCallback
  = OutlineOutputCallback
    { runCallback :: OutlineEntry -> TCM ()
    }

instance NFData OutlineOutputCallback where
  rnf (OutlineOutputCallback !e) = ()

instance NFData OutlinePending where
  rnf (OutlinePending r c s t) = rnf (r, c, s, t)

defaultOutlineOutputCallback :: OutlineOutputCallback
defaultOutlineOutputCallback = OutlineOutputCallback $ const $ pure ()

recordTypeInContext
  :: ( HasOptions m
     , MonadTCState m
     , MonadTCEnv m
     , ReadTCState m
     , MonadTCM m
     )
  => Range -> Type
  -> m ()
recordTypeInContext range ty = do
  ctx <- reverse <$> getContext
  scope <- getScope
  let
    pending = OutlinePending
      { outlineRange   = Range.rangeToRange range
      , outlineContext = ctx
      , outlineScope   = scope
      , outlineType    = ty
      }
  clo <- buildClosure pending
  modifyTCLens' stPendingOutline (clo:)

flushPendingOutline :: TCM ()
flushPendingOutline = do
  t <- getsTC (view stPendingOutline)
  callback <- getsTC (runCallback . stOutlineOutputCallback . stPersistentState)
  traverse_ (flip enterClosure (callback <=< finishOutline)) t
  modifyTCLens' stPendingOutline $ const []

finishOutline :: OutlinePending -> TCM OutlineEntry
finishOutline OutlinePending{..} = do
  withScope_ outlineScope $ do
    outlineContext <- runReduceM $ traverse (traverse (traverse instantiateFull')) outlineContext
    outlineType <- runReduceM $ instantiateFull' outlineType
    relevant <- flip namesIn' (fmap (fmap snd) outlineContext, outlineType) $ \nm -> do
      thedef <- getConstInfo nm
      ty <- showit (defType thedef)
      nm' <- showit nm
      let
        bs = Range.rangeToRange (nameBindingSite (qnameName (defName thedef)))
        NameId _ modh = nameId (qnameName (defName thedef))

      mod <- iTopLevelModuleName . miInterface . fromMaybe __IMPOSSIBLE__ <$>
        getVisitedModule (TopLevelModuleName noRange modh (mempty :| []))
      let
        gbl = OutlineGlobal
          { globalNameId = nameId (qnameName nm)
          , globalType   = ty
          , globalStart  = Range.from bs
          , globalEnd    = Range.to bs
          , globalMod    = mod
          }
      pure (HashMap.singleton nm' gbl)
    (ctx_e, ty) <- go outlineContext outlineType
    mod <- fromMaybe __IMPOSSIBLE__ <$> currentTopLevelModule
    pure $ OutlineEntry
      { entryStart    = Range.from outlineRange
      , entryEnd      = Range.to outlineRange
      , entryMod      = mod
      , entryType     = ty
      , entryContext  = ctx_e
      , entryRelevant = relevant
      }
  where
    showit :: PrettyTCM a => a -> TCM Text
    showit = fmap (Text.pack . P.renderStyle P.style{P.mode=P.OneLineMode}) . prettyTCM

    go :: Context -> Type -> TCM (HashMap.HashMap Text Text, Text)
    go [] t = do
      t <- showit t
      pure (mempty, t)
    go (x:xs) t = do
      let (nm, ty) = unDom x
      ty <- showit ty
      nm <- showit nm
      addContext x $ do
        (rest, t) <- go xs t
        pure (HashMap.insert nm ty rest, t)


jsonOutlineOutputCallback :: AbsolutePath -> OutlineOutputCallback
jsonOutlineOutputCallback fp =
  OutlineOutputCallback $ \obj -> do
    liftIO $ withFile (filePath fp) AppendMode $ \h -> do
      hPutChar h '\30' -- Record separator
      Bsl.hPutStr h $ encode obj
      hPutChar h '\n'
