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
import Agda.Utils.Lens

import Agda.Syntax.Scope.Base
import Agda.Syntax.Position
import Agda.Syntax.Internal ( Type )

import Control.Monad.IO.Class
import Control.DeepSeq
import Control.Monad

data OutlineEntry
  = OutlineEntry
    { outlineRange   :: {-# UNPACK #-} !Range.Range
    , outlineContext :: Context
    , outlineScope   :: {-# UNPACK #-} !ScopeInfo
    , outlineType    :: {-# UNPACK #-} !Type
    }

data OutlineOutputCallback
  = OutlineOutputCallback
    { runCallback :: [Closure OutlineEntry] -> TCM ()
    }

instance NFData OutlineOutputCallback where
  rnf (OutlineOutputCallback !e) = ()

instance NFData OutlineEntry where
  rnf (OutlineEntry r c s t) = rnf (r, c, s, t)

recordTypeInContext
  :: ( HasOptions m
     , MonadTCState m
     , MonadTCEnv m
     , ReadTCState m
     , MonadTCM m
     )
  => Range -> Type
  -> m ()
recordTypeInContext range ty = getsTC (stOutlineOutputCallback . stPersistentState) >>= \case
  Just _ -> do
    ctx <- reverse <$> getContext
    scope <- getScope
    let
      pending = OutlineEntry
        { outlineRange   = Range.rangeToRange range
        , outlineContext = ctx
        , outlineScope   = scope
        , outlineType    = ty
        }
    clo <- buildClosure pending
    modifyTCLens' stPendingOutline (clo:)
  Nothing -> pure ()

flushPendingOutline :: TCM ()
flushPendingOutline = getsTC (stOutlineOutputCallback . stPersistentState) >>= \case
  Just (OutlineOutputCallback cb) -> do
    t <- getsTC (view stPendingOutline)
    modifyTCLens' stPendingOutline $ const []
    cb t
  Nothing -> pure ()
