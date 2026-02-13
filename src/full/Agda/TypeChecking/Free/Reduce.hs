{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Agda.TypeChecking.Free.Reduce
  ( ForceNotFree
  , forceNotFree
  , reallyFree
  , New.IsFree(..)
  , nonFreeVars
  ) where

import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Precompute
import Agda.Syntax.Position

-- import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.VarSet as VarSet
import Agda.Utils.VarSet (VarSet)
import Agda.Utils.StrictState
import Agda.Utils.StrictReader

import Agda.TypeChecking.Free.ReduceNew qualified as New
import Agda.TypeChecking.Free.ReduceOld qualified as Old
import Agda.Utils.Impossible

import Debug.Trace

type IsFree = New.IsFree
type ForceNotFree a = (Old.ForceNotFree a, New.ForceNotFree a)

instance KillRange (IntMap IsFree) where
  killRange x = x

forceNotFree :: (Eq a, KillRange a, Show a, ForceNotFree a, Reduce a) => VarSet -> a -> ReduceM (IntMap IsFree, a)
forceNotFree xs a = do
  -- traceM "\n\nOLD FORCEFREE START\n\n"
  -- res <- Old.forceNotFree xs a
  -- pure res
  -- traceM "\n\nNEW FORCEFREE START\n\n"
  res' <- New.forceNotFree xs a
  -- if fst res /= fst res' then do
  --   traceM "INPUT"
  --   traceM (show xs)
  --   traceM (show $ killRange a)

  --   traceM "\n\nREDUCED INPUT"
  --   traceM (show xs)
  --   a' <- reduce =<< reduce =<< reduce a
  --   traceM (show $ killRange a')

  --   traceM "\nOLDOUT"
  --   traceShowM (fst res)
  --   -- traceM (show $ killRange res)

  --   traceM "\nNEWOUT"
  --   traceShowM (fst res')
  --   -- traceM (show $ killRange res')

  --   error "FORCENFREE"

  -- else
  pure res'

reallyFree :: (Eq a, Show a, Reduce a, ForceNotFree a) => VarSet -> a -> ReduceM (Either Blocked_ (Maybe a))
reallyFree xs a = do
  -- res  <- Old.reallyFree xs a
  -- pure res
  res' <- New.reallyFree xs a
  -- if res /= res' then do
  --   error "REALLYFREE"
  -- else
  pure res'

nonFreeVars :: IntMap IsFree -> VarSet
nonFreeVars xs =
  -- let res  = Old.nonFreeVars xs in
  -- -- res
  let res' = New.nonFreeVars xs in
  -- if res /= res' then
  --   error "NONFREEVARS"
  -- else
    res'
