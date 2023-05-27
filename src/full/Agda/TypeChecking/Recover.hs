-- | Implements recovery from type errors.
module Agda.TypeChecking.Recover where

import Control.Monad.Except

import qualified Data.Set as Set

import Agda.Syntax.Position
import Agda.Syntax.Internal

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad

import Agda.Utils.Permutation
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Lens

-- import GHC.Stack (CallStack)

deferCheckingError :: Type -> TCM Term -> TCM Term
deferCheckingError ty continue = ifM (asksTC envRecoveryAllowed) recover continue where
  recover = continue `catchError` \case
    TypeError loc state err -> do
      reportSDoc "tc.error.defer" 20 $ vcat
        [ "Deferring type error:" $$ prettyTCM (TypeError loc state err)
        , "Current task:" $$ (text . show =<< asksTC envCurrentTask)
        ]

      setTCLens stTCWarnings (state ^. stTCWarnings)

      printed <- prettyTCM (TypeError loc state err)
      addWarning TCWarning
        { tcWarningLocation       = loc
        , tcWarningRange          = envRange $ clEnv err
        , tcWarning               = DeferredTypeError loc state err
        , tcWarningPrintedWarning = printed
        , tcWarningCached         = True
        }
      asksTC envCurrentTask >>=
        modifyTCLens' stFailedTasks . Set.insert

      -- Create the metavariable standing for the expression that failed.
      -- Note: the context for the meta is not the context of the type
      -- error; it is the context of the type-checking computation. The
      -- type error may have happened in a different context, e.g. from
      -- the conversion checker introducing a lambda.
      newDeferralToken ty
    e -> throwError e

newDeferralToken :: Type -> TCM Term
newDeferralToken ty = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  i <- createMetaInfo' DontRunMetaOccursCheck
  m <- newMeta' DeferredError Instantiable i normalMetaPriority (idP (size tel))
      $ HasType () CmpLeq $ telePi_ tel ty
  let token = MetaV m $ map Apply vs
  reportSDoc "tc.error.defer" 20 $ "Deferral token:" <+> prettyTCM token
  pure token

inNewTask :: TCM a -> TCM a
inNewTask cont = do
  tid <- fresh
  localTC (\e -> e { envCurrentTask = tid }) cont

-- TODO: Use the current task instead? What if a parent task failed?
hasDeferredErrors :: TCM Bool
hasDeferredErrors = do
  warns <- useTC stTCWarnings
  let
    is TCWarning { tcWarning = DeferredTypeError{} } = True
    is _ = False
  pure $ any is warns
