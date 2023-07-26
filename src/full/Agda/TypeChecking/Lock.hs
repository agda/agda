{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Lock
  ( isTimeless
  , checkLockedVars
  , checkEarlierThan
  )
where

import Control.Monad            ( filterM, forM, forM_ )

import qualified Data.IntMap as IMap
import qualified Data.IntSet as ISet
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Constraints () -- instance MonadConstraint TCM
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Free

import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.VarSet as VSet
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size

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
  -- Have to instantiate the lock, otherwise we might block on it even
  -- after it's been solved (e.g.: it's an interaction point, see #6528)
  lk <- instantiate lk
  reportSDoc "tc.term.lock" 40 $ "Checking locked vars.."
  reportSDoc "tc.term.lock" 50 $ nest 2 $ vcat
     [ text "t     = " <+> pretty t
     , text "ty    = " <+> pretty ty
     , text "lk    = " <+> pretty lk
     , text "lk_ty = " <+> pretty lk_ty
     ]

  -- Strategy: compute allowed variables, check that @t@ doesn't use more.
  mi <- getLockVar (unArg lk)
  caseMaybe mi (typeError (DoesNotMentionTicks t ty lk)) $ \ i -> do

  cxt <- getContext
  let toCheck = zip [0..] $ zipWith raise [1..] (take i cxt)

  let fv = freeVarsIgnore IgnoreInAnnotations (t,ty)
  let
    rigid = rigidVars fv
    -- flexible = IMap.keysSet $ flexibleVars fv
    termVars = allVars fv -- ISet.union rigid flexible
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
    -- flexVars = flexibleVars fv
    -- blockingMetas = map (`lookupVarMap` flexVars) (ISet.toList $ termVars ISet.\\ allowedVars)
  if ISet.null illegalVars then  -- only flexible vars are infringing
    -- TODO: be more precise about which metas
    -- flexVars = flexibleVars fv
    -- blockingMetas = map (`lookupVarMap` flexVars) (ISet.toList $ termVars ISet.\\ allowedVars)
    patternViolation alwaysUnblock
  else
    typeError $ ReferencesFutureVariables t (List1.fromList (ISet.toList illegalVars)) lk i
    -- List1.fromList is guarded by not (null illegalVars)


getLockVar :: Term -> TCMT IO (Maybe Int)
getLockVar lk = do
  let
    fv = freeVarsIgnore IgnoreInAnnotations lk
    flex = flexibleVars fv

    isLock i = fmap (getLock . domInfo) (lookupBV i) <&> \case
      IsLock{} -> True
      IsNotLock{} -> False

  unless (IMap.null flex) $ do
    let metas = Set.unions $ map (foldrMetaSet Set.insert Set.empty) $ IMap.elems flex
    patternViolation $ unblockOnAnyMeta metas

  is <- filterM isLock $ ISet.toList $ rigidVars fv

  -- Out of the lock variables that appear in @lk@ the one in the
  -- left-most position in the context is what will determine the
  -- available context for the head.
  let mi | Prelude.null is   = Nothing
         | otherwise = Just $ maximum is

  pure mi

isTimeless :: Type -> TCM Bool
isTimeless t = do
  t <- abortIfBlocked t
  timeless <- mapM getName' [builtinInterval, builtinIsOne]
  case unEl t of
    Def q _ | Just q `elem` timeless -> return True
    _                                -> return False

notAllowedVarsError :: Term -> [Int] -> TCM b
notAllowedVarsError lk is = do
        typeError . GenericDocError =<<
         ("The following vars are not allowed in a later value applied to"
          <+> prettyTCM lk <+> ":" <+> prettyTCM (map var $ is))

checkEarlierThan :: Term -> VSet.VarSet -> TCM ()
checkEarlierThan lk fvs = do
  mv <- getLockVar lk
  caseMaybe mv (return ()) $ \ i -> do
    let problems = filter (<= i) $ VSet.toList fvs
    forM_ problems $ \ j -> do
      ty <- typeOfBV j
      unlessM (isTimeless ty) $
        notAllowedVarsError lk [j]
