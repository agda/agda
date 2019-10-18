{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.Lock where

import Control.Arrow (first, second)
import Control.Monad.Reader

import qualified Data.Map as Map
import qualified Data.IntMap as IMap
import qualified Data.IntSet as ISet

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free

import Agda.Utils.Function
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible



checkLockedVars
  :: Term
     -- ^ term to check
  -> Type
     -- ^ its type
  -> Arg Term
     -- ^ the lock
  -> Type
     -- ^ type of the lock
  -> TCM ()
checkLockedVars t ty lk lk_ty = catchConstraint (CheckLockedVars t ty lk lk_ty) $ do
  reportSDoc "tc.term.lock" 40 $ "Checking locked vars.."
  reportSDoc "tc.term.lock" 50 $ nest 2 $ vcat
     [ text "t     = " <+> pretty t
     , text "ty    = " <+> pretty ty
     , text "lk    = " <+> pretty lk
     , text "lk_ty = " <+> pretty lk_ty
     ]

  -- Strategy: compute allowed variables, check that @t@ doesn't use more.
  mv <- isVar =<< reduce (unArg lk)
  caseMaybe mv noVar $ \ i -> do

  isLock i

  cxt <- getContext
  let toCheck = zip [0..] $ zipWith raise [1..] (take i cxt)

  let fv = freeVarsIgnore IgnoreInAnnotations t
  let
    rigid = rigidVars fv
    flexible = IMap.keysSet $ flexibleVars fv
    termVars = ISet.union rigid flexible
    earlierVars = ISet.fromList [i+1 .. size cxt - 1]
  if termVars `ISet.isSubsetOf` earlierVars then return () else do

  checked <- fmap catMaybes . forM toCheck $ \ (j,dom) -> do
    ifM (isTimeless (snd . unDom $ dom))
        (return $ Just j)
        (return $ Nothing)

  let allowedVars = ISet.union earlierVars (ISet.fromList checked)

  if termVars `ISet.isSubsetOf` allowedVars then return () else do
  let
    illegalVars = rigid ISet.\\ allowedVars
  if ISet.null illegalVars then patternViolation -- only flexible vars are infringing
  else do
    typeError . GenericDocError =<<
         ("The following vars are not allowed in a later value applied to"
          <+> prettyTCM lk <+> ":" <+> prettyTCM (map var $ ISet.toList illegalVars))
  where
    isVar (Var l []) = return $ Just l
    isVar (MetaV{}) = patternViolation
    isVar _ = return $ Nothing
    noVar = typeError $ GenericError "lock should be a var"
    isLock i = do
      islock <- getLock . domInfo <$> lookupBV i
      unless (islock == IsLock) $
        typeError $ GenericError "Cannot eliminate with non-lock variable."

isTimeless :: Type -> TCM Bool
isTimeless t = do
  ifBlockedType t (\ _ _ -> patternViolation) $ \ _ t -> do
  timeless <- mapM getName' [builtinInterval, builtinIsOne]
  case unEl t of
    Def q _ | Just q `elem` timeless -> return True
    _                                -> return False
