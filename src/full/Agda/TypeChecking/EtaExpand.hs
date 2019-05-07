
-- | Compute eta long normal forms.
module Agda.TypeChecking.EtaExpand where

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Monad

import Agda.Utils.Impossible

-- | Eta-expand a term if its type is a function type or an eta-record type.
etaExpandOnce
  :: (MonadReduce m, MonadTCEnv m, HasOptions m, HasConstInfo m, MonadDebug m)
  => Type -> Term -> m Term
etaExpandOnce a v = reduce a >>= \case
  El _ (Pi a b) -> return $
    Lam ai $ mkAbs (absName b) $ raise 1 v `apply` [ Arg ai $ var 0 ]
    where ai = domInfo a

  a -> isEtaRecordType a >>= \case
    Just (r, pars) -> do
      def <- theDef <$> getConstInfo r
      (_, con, ci, args) <- etaExpandRecord_ r pars def v
      return $ mkCon con ci args
    Nothing -> return v

-- | Eta-expand functions and expressions of eta-record
-- type wherever possible.
deepEtaExpand :: Term -> Type -> TCM Term
deepEtaExpand = checkInternal' etaExpandAction

etaExpandAction
  :: (MonadReduce m, MonadTCEnv m, HasOptions m, HasConstInfo m, MonadDebug m)
  => Action m
etaExpandAction = Action
  { preAction       = etaExpandOnce
  , postAction      = \ _ -> return
  , relevanceAction = \ _ -> id
  }
