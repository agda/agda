{-# LANGUAGE CPP #-}

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

#include "undefined.h"
import Agda.Utils.Impossible

-- | Eta-expand a term if its type is a function type or an eta-record type.
etaExpandOnce :: Type -> Term -> TCM Term
etaExpandOnce a v = reduce a >>= \case
  El _ (Pi a b) -> return $
    Lam (domInfo a) $ mkAbs (absName b) $ raise 1 v `apply1` var 0

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

etaExpandAction :: Action
etaExpandAction = Action
  { preAction       = etaExpandOnce
  , postAction      = \ _ -> return
  , relevanceAction = \ _ -> id
  }
