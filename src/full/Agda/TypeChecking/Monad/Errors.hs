module Agda.TypeChecking.Monad.Errors where

import Control.Monad.Except

import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Internal


import Agda.Utils.Permutation
import Agda.Utils.Size

import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Pretty
import Data.List.NonEmpty (NonEmpty(..))
import Agda.TypeChecking.Warnings
import Agda.Utils.Monad
import Agda.TypeChecking.Monad.Closure
import GHC.Stack (CallStack)

guardingTypeErrors :: Type -> TCM Term -> TCM Term
guardingTypeErrors want m = m `catchError` \case
  TypeError stack state err -> recoverTypeError stack state err want
  e -> throwError e

recoverTypeError :: CallStack -> TCState -> Closure TypeError -> Type -> TCM Term
recoverTypeError stack state err want = do
  i   <- createMetaInfo' DontRunMetaOccursCheck
  tel <- getContextTelescope
  m   <- newMeta' RecoveredTypeError Frozen i normalMetaPriority (idP (size tel)) $
    HasType () CmpLeq want
  reportSDoc "tc.error.recover" 10 $
    "created meta variable" <+> prettyTCM m <+> "to recover from" <+> prettyTCM err
  ifM (isErrorFromRecovery err)
    (reportSDoc "tc.error.recover" 10 $ "... but it will not become a warning")
    (do err_doc <- prettyTCM (TypeError stack state err)
        addWarning . TCWarning
          stack
          (envRange $ clEnv err)
          (RecoveredTypeErrorW (TypeError stack state err))
          err_doc =<< useR stAreWeCaching)

  MetaV m . fmap Apply <$> getContextArgs

-- | Did the given type error happen because we recovered from another
-- type error? In that case, we shouldn't add it as a warning, to
-- prevent cascading.
isErrorFromRecovery :: Closure TypeError -> TCM Bool
isErrorFromRecovery cl = enterClosure cl $ \err -> orM [errorCall] where
  isErrorMeta mid = lookupMetaInstantiation mid >>= \case
    RecoveredTypeError -> pure True
    _ -> pure False

  errorCall = asksTC (fmap clValue . envCall) >>= \case
    Just (CheckMetaSolution _ mid _ _) -> isErrorMeta mid
    _ -> pure False
