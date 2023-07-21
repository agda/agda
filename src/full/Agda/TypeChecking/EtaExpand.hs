{-# OPTIONS_GHC -Wunused-imports #-}

-- | Compute eta long normal forms.
module Agda.TypeChecking.EtaExpand where

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

-- | Eta-expand a term if its type is a function type or an eta-record type.
etaExpandOnce :: PureTCM m => Type -> Term -> m Term
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
deepEtaExpand v a = checkInternal' etaExpandAction v CmpLeq a

etaExpandAction :: PureTCM m => Action m
etaExpandAction = defaultAction { preAction = etaExpandOnce  }
