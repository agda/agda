{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE GADTs #-}

module Agda.TypeChecking.MetaVars where

import Prelude hiding (null)

import Control.Monad.Reader

import Data.Function
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Foldable as Fold
import qualified Data.Traversable as Trav

import Agda.Interaction.Options

import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic
import Agda.Syntax.Position (killRange)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Free
import Agda.TypeChecking.Level
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.SizedTypes (boundedSizeMetaHook, isSizeProblem)
import {-# SOURCE #-} Agda.TypeChecking.CheckInternal
import {-# SOURCE #-} Agda.TypeChecking.Conversion

-- import Agda.TypeChecking.CheckInternal
-- import {-# SOURCE #-} Agda.TypeChecking.CheckInternal (checkInternal)
import Agda.TypeChecking.MetaVars.Occurs

import Agda.Utils.Except
  ( ExceptT
  , MonadError(throwError)
  , runExceptT
  )

import Agda.Utils.Function
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Permutation
import Agda.Utils.Pretty ( prettyShow, render )
import qualified Agda.Utils.VarSet as Set

#include "undefined.h"
import Agda.Utils.Impossible

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
--   @reverse@ is necessary because we are directly abstracting over the list.
--
findIdx :: Eq a => [a] -> a -> Maybe Int
findIdx vs v = List.findIndex (==v) (reverse vs)

-- | Check whether a meta variable is a place holder for a blocked term.
isBlockedTerm :: MetaId -> TCM Bool
isBlockedTerm x = do
    reportSLn "tc.meta.blocked" 12 $ "is " ++ prettyShow x ++ " a blocked term? "
    i <- mvInstantiation <$> lookupMeta x
    let r = case i of
            BlockedConst{}                 -> True
            PostponedTypeCheckingProblem{} -> True
            InstV{}                        -> False
            Open{}                         -> False
            OpenInstance{}                 -> False
    reportSLn "tc.meta.blocked" 12 $
      if r then "  yes, because " ++ show i else "  no"
    return r

isEtaExpandable :: [MetaKind] -> MetaId -> TCM Bool
isEtaExpandable kinds x = do
    i <- mvInstantiation <$> lookupMeta x
    return $ case i of
      Open{}                         -> True
      OpenInstance{}                 -> notElem Records kinds
      InstV{}                        -> False
      BlockedConst{}                 -> False
      PostponedTypeCheckingProblem{} -> False

-- * Performing the assignment

-- | Performing the meta variable assignment.
--
--   The instantiation should not be an 'InstV' and the 'MetaId'
--   should point to something 'Open' or a 'BlockedConst'.
--   Further, the meta variable may not be 'Frozen'.
assignTerm :: MetaId -> [Arg ArgName] -> Term -> TCM ()
assignTerm x tel v = do
     -- verify (new) invariants
    whenM (isFrozen x) __IMPOSSIBLE__
    assignTerm' x tel v

-- | Skip frozen check.  Used for eta expanding frozen metas.
assignTerm' :: MetaId -> [Arg ArgName] -> Term -> TCM ()
assignTerm' x tel v = do
    reportSLn "tc.meta.assign" 70 $ prettyShow x ++ " := " ++ show v ++ "\n  in " ++ show tel
     -- verify (new) invariants
    whenM (not <$> asksTC envAssignMetas) __IMPOSSIBLE__

    verboseS "profile.metas" 10 $ liftTCM $ tickMax "max-open-metas" . (fromIntegral . size) =<< getOpenMetas
    modifyMetaStore $ ins x $ InstV tel $ killRange v
    etaExpandListeners x
    wakeupConstraints x
    reportSLn "tc.meta.assign" 20 $ "completed assignment of " ++ prettyShow x
  where
    ins x i = IntMap.adjust (\ mv -> mv { mvInstantiation = i }) $ metaId x

-- * Creating meta variables.

-- | Create a sort meta that cannot be instantiated with 'Inf' (Setω).
newSortMetaBelowInf :: TCM Sort
newSortMetaBelowInf = do
  x <- newSortMeta
  hasBiggerSort x
  return x

-- | Create a sort meta that may be instantiated with 'Inf' (Setω).
newSortMeta :: TCM Sort
newSortMeta =
  ifM hasUniversePolymorphism (newSortMetaCtx =<< getContextArgs)
  -- else (no universe polymorphism)
  $ do i   <- createMetaInfo
       x   <- newMeta i normalMetaPriority (idP 0) $ IsSort () __DUMMY_TYPE__
       return $ MetaS x []

-- | Create a sort meta that may be instantiated with 'Inf' (Setω).
newSortMetaCtx :: Args -> TCM Sort
newSortMetaCtx vs = do
    i   <- createMetaInfo
    tel <- getContextTelescope
    let t = telePi_ tel __DUMMY_TYPE__
    x   <- newMeta i normalMetaPriority (idP $ size tel) $ IsSort () t
    reportSDoc "tc.meta.new" 50 $
      "new sort meta" <+> prettyTCM x <+> ":" <+> prettyTCM t
    return $ MetaS x $ map Apply vs

newTypeMeta :: Sort -> TCM Type
newTypeMeta s = El s . snd <$> newValueMeta RunMetaOccursCheck (sort s)

newTypeMeta_ ::  TCM Type
newTypeMeta_  = newTypeMeta =<< (workOnTypes $ newSortMeta)
-- TODO: (this could be made work with new uni-poly)
-- Andreas, 2011-04-27: If a type meta gets solved, than we do not have to check
-- that it has a sort.  The sort comes from the solution.
-- newTypeMeta_  = newTypeMeta Inf

-- | @newInstanceMeta s t cands@ creates a new instance metavariable
--   of type the output type of @t@ with name suggestion @s@.
newInstanceMeta :: MetaNameSuggestion -> Type -> TCM (MetaId, Term)
newInstanceMeta s t = do
  vs  <- getContextArgs
  ctx <- getContextTelescope
  newInstanceMetaCtx s (telePi_ ctx t) vs

newInstanceMetaCtx :: MetaNameSuggestion -> Type -> Args -> TCM (MetaId, Term)
newInstanceMetaCtx s t vs = do
  reportSDoc "tc.meta.new" 50 $ fsep
    [ "new instance meta:"
    , nest 2 $ prettyTCM vs <+> "|-"
    ]
  -- Andreas, 2017-10-04, issue #2753: no metaOccurs check for instance metas
  i0 <- createMetaInfo' DontRunMetaOccursCheck
  let i = i0 { miNameSuggestion = s }
  TelV tel _ <- telView t
  let perm = idP (size tel)
  x <- newMeta' OpenInstance i normalMetaPriority perm (HasType () t)
  reportSDoc "tc.meta.new" 50 $ fsep
    [ nest 2 $ pretty x <+> ":" <+> prettyTCM t
    ]
  let c = FindInstance x Nothing Nothing
  -- If we're not already solving instance constraints we should add this
  -- to the awake constraints to make sure we don't forget about it. If we
  -- are solving constraints it will get woken up later (see #2690)
  ifM isSolvingConstraints (addConstraint c) (addAwakeConstraint' c)
  etaExpandMetaSafe x
  return (x, MetaV x $ map Apply vs)

-- | Create a new value meta with specific dependencies, possibly η-expanding in the process.
newNamedValueMeta :: RunMetaOccursCheck -> MetaNameSuggestion -> Type -> TCM (MetaId, Term)
newNamedValueMeta b s t = do
  (x, v) <- newValueMeta b t
  setMetaNameSuggestion x s
  return (x, v)

-- | Create a new value meta with specific dependencies without η-expanding.
newNamedValueMeta' :: RunMetaOccursCheck -> MetaNameSuggestion -> Type -> TCM (MetaId, Term)
newNamedValueMeta' b s t = do
  (x, v) <- newValueMeta' b t
  setMetaNameSuggestion x s
  return (x, v)

-- | Create a new metavariable, possibly η-expanding in the process.
newValueMeta :: RunMetaOccursCheck -> Type -> TCM (MetaId, Term)
newValueMeta b t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx b t tel (idP $ size tel) vs

newValueMetaCtx :: RunMetaOccursCheck -> Type -> Telescope -> Permutation -> Args -> TCM (MetaId, Term)
newValueMetaCtx b t tel perm ctx =
  mapSndM instantiateFull =<< newValueMetaCtx' b t tel perm ctx

-- | Create a new value meta without η-expanding.
newValueMeta' :: RunMetaOccursCheck -> Type -> TCM (MetaId, Term)
newValueMeta' b t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx' b t tel (idP $ size tel) vs

-- | Create a new value meta with specific dependencies.
newValueMetaCtx' :: RunMetaOccursCheck -> Type -> Telescope -> Permutation -> Args -> TCM (MetaId, Term)
newValueMetaCtx' b a tel perm vs = do
  i <- createMetaInfo' b
  let t     = telePi_ tel a
  x <- newMeta i normalMetaPriority perm (HasType () t)
  reportSDoc "tc.meta.new" 50 $ fsep
    [ "new meta:"
    , nest 2 $ prettyTCM vs <+> "|-"
    , nest 2 $ pretty x <+> ":" <+> prettyTCM t
    ]
  etaExpandMetaSafe x
  -- Andreas, 2012-09-24: for Metas X : Size< u add constraint X+1 <= u
  let u = MetaV x $ map Apply vs
  boundedSizeMetaHook u tel a
  return (x, u)

newTelMeta :: Telescope -> TCM Args
newTelMeta tel = newArgsMeta (abstract tel $ __DUMMY_TYPE__)

type Condition = Dom Type -> Abs Type -> Bool

trueCondition :: Condition
trueCondition _ _ = True

newArgsMeta :: Type -> TCM Args
newArgsMeta = newArgsMeta' trueCondition

newArgsMeta' :: Condition -> Type -> TCM Args
newArgsMeta' condition t = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newArgsMetaCtx' condition t tel (idP $ size tel) args

newArgsMetaCtx :: Type -> Telescope -> Permutation -> Args -> TCM Args
newArgsMetaCtx = newArgsMetaCtx' trueCondition

newArgsMetaCtx' :: Condition -> Type -> Telescope -> Permutation -> Args -> TCM Args
newArgsMetaCtx' condition (El s tm) tel perm ctx = do
  tm <- reduce tm
  case tm of
    Pi dom@(Dom{domInfo = info, unDom = a}) codom | condition dom codom -> do
      let mod  = getModality info
          -- Issue #3031: It's not enough to applyModalityToContext, since most (all?)
          -- of the context lives in tel. Don't forget the arguments in ctx.
          tel' = telFromList . map (mod `inverseApplyModality`) . telToList $ tel
          ctx' = (map . mapModality) (mod `inverseComposeModality`) ctx
      (m, u) <- applyModalityToContext info $
                 newValueMetaCtx RunMetaOccursCheck a tel' perm ctx'
      setMetaArgInfo m (getArgInfo dom)
      args <- newArgsMetaCtx' condition (codom `absApp` u) tel perm ctx
      return $ Arg info u : args
    _  -> return []

-- | Create a metavariable of record type. This is actually one metavariable
--   for each field.
newRecordMeta :: QName -> Args -> TCM Term
newRecordMeta r pars = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newRecordMetaCtx r pars tel (idP $ size tel) args

newRecordMetaCtx :: QName -> Args -> Telescope -> Permutation -> Args -> TCM Term
newRecordMetaCtx r pars tel perm ctx = do
  ftel   <- flip apply pars <$> getRecordFieldTypes r
  fields <- newArgsMetaCtx (telePi_ ftel __DUMMY_TYPE__) tel perm ctx
  con    <- getRecordConstructor r
  return $ Con con ConOSystem (map Apply fields)

newQuestionMark :: InteractionId -> Type -> TCM (MetaId, Term)
newQuestionMark = newQuestionMark' $ newValueMeta' RunMetaOccursCheck

newQuestionMark' :: (Type -> TCM (MetaId, Term)) -> InteractionId -> Type -> TCM (MetaId, Term)
newQuestionMark' new ii t = do
  -- Andreas, 2016-07-29, issue 1720-2
  -- This is slightly risky, as the same interaction id
  -- maybe be shared between different contexts.
  -- Blame goes to the record processing hack, see issue #424
  -- and @ConcreteToAbstract.recordConstructorType@.
  let existing x = (x,) . MetaV x . map Apply <$> getContextArgs
  flip (caseMaybeM $ lookupInteractionMeta ii) existing $ {-else-} do

  -- Do not run check for recursive occurrence of meta in definitions,
  -- because we want to give the recursive solution interactively (Issue 589)
  (x, m) <- new t
  connectInteractionPoint ii x
  return (x, m)

-- | Construct a blocked constant if there are constraints.
blockTerm :: Type -> TCM Term -> TCM Term
blockTerm t blocker = do
  (pid, v) <- newProblem blocker
  blockTermOnProblem t v pid

blockTermOnProblem :: Type -> Term -> ProblemId -> TCM Term
blockTermOnProblem t v pid =
  -- Andreas, 2012-09-27 do not block on unsolved size constraints
  ifM (isProblemSolved pid `or2M` isSizeProblem pid) (return v) $ do
    i   <- createMetaInfo
    es  <- map Apply <$> getContextArgs
    tel <- getContextTelescope
    x   <- newMeta' (BlockedConst $ abstract tel v)
                    i lowMetaPriority (idP $ size tel)
                    (HasType () $ telePi_ tel t)
                    -- we don't instantiate blocked terms
    inTopContext $ addConstraint (Guarded (UnBlock x) pid)
    reportSDoc "tc.meta.blocked" 20 $ vcat
      [ "blocked" <+> prettyTCM x <+> ":=" <+> inTopContext (prettyTCM $ abstract tel v)
      , "     by" <+> (prettyTCM =<< getConstraintsForProblem pid) ]
    inst <- isInstantiatedMeta x
    case inst of
      True  -> instantiate (MetaV x es)
      False -> do
        -- We don't return the blocked term instead create a fresh metavariable
        -- that we compare against the blocked term once it's unblocked. This way
        -- blocked terms can be instantiated before they are unblocked, thus making
        -- constraint solving a bit more robust against instantiation order.
        -- Andreas, 2015-05-22: DontRunMetaOccursCheck to avoid Issue585-17.
        (_, v) <- newValueMeta DontRunMetaOccursCheck t
        i   <- liftTCM fresh
        -- This constraint is woken up when unblocking, so it doesn't need a problem id.
        cmp <- buildProblemConstraint_ (ValueCmp CmpEq t v (MetaV x es))
        listenToMeta (CheckConstraint i cmp) x
        return v

blockTypeOnProblem :: Type -> ProblemId -> TCM Type
blockTypeOnProblem (El s a) pid = El s <$> blockTermOnProblem (El Inf $ Sort s) a pid

-- | @unblockedTester t@ returns @False@ if @t@ is a meta or a blocked term.
--
--   Auxiliary function to create a postponed type checking problem.
unblockedTester :: Type -> TCM Bool
unblockedTester t = ifBlockedType t (\ m t -> return False) (\ _ t -> return True)

-- | Create a postponed type checking problem @e : t@ that waits for type @t@
--   to unblock (become instantiated or its constraints resolved).
postponeTypeCheckingProblem_ :: TypeCheckingProblem -> TCM Term
postponeTypeCheckingProblem_ p = do
  postponeTypeCheckingProblem p (unblock p)
  where
    unblock (CheckExpr _ _ t)         = unblockedTester t
    unblock (CheckArgs _ _ _ t _ _)   = unblockedTester t  -- The type of the head of the application.
    unblock (CheckProjAppToKnownPrincipalArg _ _ _ _ _ _ _ _ t) = unblockedTester t -- The type of the principal argument
    unblock (CheckLambda _ _ _ t)     = unblockedTester t
    unblock (UnquoteTactic _ _ _)     = __IMPOSSIBLE__     -- unquote problems must be supply their own tester
    unblock (DoQuoteTerm _ _ _)       = __IMPOSSIBLE__     -- also quoteTerm problems

-- | Create a postponed type checking problem @e : t@ that waits for conditon
--   @unblock@.  A new meta is created in the current context that has as
--   instantiation the postponed type checking problem.  An 'UnBlock' constraint
--   is added for this meta, which links to this meta.
postponeTypeCheckingProblem :: TypeCheckingProblem -> TCM Bool -> TCM Term
postponeTypeCheckingProblem p unblock = do
  i   <- createMetaInfo' DontRunMetaOccursCheck
  tel <- getContextTelescope
  cl  <- buildClosure p
  let t = problemType p
  m   <- newMeta' (PostponedTypeCheckingProblem cl unblock)
                  i normalMetaPriority (idP (size tel))
         $ HasType () $ telePi_ tel t

  -- Create the meta that we actually return
  -- Andreas, 2012-03-15
  -- This is an alias to the pptc meta, in order to allow pruning (issue 468)
  -- and instantiation.
  -- Since this meta's solution comes from user code, we do not need
  -- to run the extended occurs check (metaOccurs) to exclude
  -- non-terminating solutions.
  es  <- map Apply <$> getContextArgs
  (_, v) <- newValueMeta DontRunMetaOccursCheck t
  cmp <- buildProblemConstraint_ (ValueCmp CmpEq t v (MetaV m es))
  i   <- liftTCM fresh
  listenToMeta (CheckConstraint i cmp) m
  addConstraint (UnBlock m)
  return v

-- | Type of the term that is produced by solving the 'TypeCheckingProblem'.
problemType :: TypeCheckingProblem -> Type
problemType (CheckExpr _ _ t         ) = t
problemType (CheckArgs _ _ _ _ t _ )   = t  -- The target type of the application.
problemType (CheckProjAppToKnownPrincipalArg _ _ _ _ _ t _ _ _) = t -- The target type of the application
problemType (CheckLambda _ _ _ t     ) = t
problemType (UnquoteTactic tac hole t) = t
problemType (DoQuoteTerm _ _ t)        = t

-- | Eta expand metavariables listening on the current meta.
etaExpandListeners :: MetaId -> TCM ()
etaExpandListeners m = do
  ls <- getMetaListeners m
  clearMetaListeners m  -- we don't really have to do this
  mapM_ wakeupListener ls

-- | Wake up a meta listener and let it do its thing
wakeupListener :: Listener -> TCM ()
  -- Andreas 2010-10-15: do not expand record mvars, lazyness needed for irrelevance
wakeupListener (EtaExpand x)         = etaExpandMetaSafe x
wakeupListener (CheckConstraint _ c) = do
  reportSDoc "tc.meta.blocked" 20 $ "waking boxed constraint" <+> prettyTCM c
  addAwakeConstraints [c]
  solveAwakeConstraints

-- | Do safe eta-expansions for meta (@SingletonRecords,Levels@).
etaExpandMetaSafe :: MetaId -> TCM ()
etaExpandMetaSafe = etaExpandMeta [SingletonRecords,Levels]

-- | Various kinds of metavariables.

data MetaKind =
    Records
    -- ^ Meta variables of record type.
  | SingletonRecords
    -- ^ Meta variables of \"hereditarily singleton\" record type.
  | Levels
    -- ^ Meta variables of level type, if type-in-type is activated.
  deriving (Eq, Enum, Bounded, Show)

-- | All possible metavariable kinds.

allMetaKinds :: [MetaKind]
allMetaKinds = [minBound .. maxBound]

-- | Eta expand a metavariable, if it is of the specified kind.
--   Don't do anything if the metavariable is a blocked term.
etaExpandMeta :: [MetaKind] -> MetaId -> TCM ()
etaExpandMeta kinds m = whenM (asksTC envAssignMetas `and2M` isEtaExpandable kinds m) $ do
  verboseBracket "tc.meta.eta" 20 ("etaExpandMeta " ++ prettyShow m) $ do
    let waitFor x = do
          reportSDoc "tc.meta.eta" 20 $ do
            "postponing eta-expansion of meta variable" <+>
              prettyTCM m <+>
              "which is blocked by" <+> prettyTCM x
          listenToMeta (EtaExpand m) x
        dontExpand = do
          reportSDoc "tc.meta.eta" 20 $ do
            "we do not expand meta variable" <+> prettyTCM m <+>
              text ("(requested was expansion of " ++ show kinds ++ ")")
    meta <- lookupMeta m
    case mvJudgement meta of
      IsSort{} -> dontExpand
      HasType _ a -> do

        reportSDoc "tc.meta.eta" 40 $ sep
          [ text "considering eta-expansion at type "
          , prettyTCM a
          , text " raw: "
          , pretty a
          ]

        TelV tel b <- telView a
        reportSDoc "tc.meta.eta" 40 $ sep
          [ text "considering eta-expansion at type"
          , addContext tel (prettyTCM b)
          , text "under telescope"
          , prettyTCM tel
          ]

        -- Eta expanding metas with a domFinite will just make sure
        -- they go unsolved: conversion will compare them at the
        -- different cases for the domain, so it will not find the
        -- solution for the whole meta.
        if any domFinite (flattenTel tel) then dontExpand else do

        -- if the target type @b@ of @m@ is a meta variable @x@ itself
        -- (@NonBlocked (MetaV{})@),
        -- or it is blocked by a meta-variable @x@ (@Blocked@), we cannot
        -- eta expand now, we have to postpone this.  Once @x@ is
        -- instantiated, we can continue eta-expanding m.  This is realized
        -- by adding @m@ to the listeners of @x@.
        ifBlocked (unEl b) (\ x _ -> waitFor x) $ \ _ t -> case t of
          lvl@(Def r es) ->
            ifM (isEtaRecord r) {- then -} (do
              let ps = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
              let expand = do
                    u <- withMetaInfo' meta $ newRecordMetaCtx r ps tel (idP $ size tel) $ teleArgs tel
                    inTopContext $ do
                      verboseS "tc.meta.eta" 15 $ do
                        du <- prettyTCM u
                        reportSDoc "tc.meta.eta" 15 $ sep
                          [ "eta expanding: " <+> pretty m <+> " --> "
                          , nest 2 $ prettyTCM u
                          ]
                      -- Andreas, 2012-03-29: No need for occurrence check etc.
                      -- we directly assign the solution for the meta
                      -- 2012-05-23: We also bypass the check for frozen.
                      noConstraints $ assignTerm' m (telToArgs tel) u  -- should never produce any constraints
              if Records `elem` kinds then
                expand
               else if (SingletonRecords `elem` kinds) then do
                 singleton <- isSingletonRecord r ps
                 case singleton of
                   Left x      -> waitFor x
                   Right False -> dontExpand
                   Right True  -> expand
                else dontExpand
            ) $ {- else -} ifM (andM [ return $ Levels `elem` kinds
                            , typeInType
                            , (Just lvl ==) <$> getBuiltin' builtinLevel
                            ]) (do
              reportSLn "tc.meta.eta" 20 $ "Expanding level meta to 0 (type-in-type)"
              -- Andreas, 2012-03-30: No need for occurrence check etc.
              -- we directly assign the solution for the meta
              noConstraints $ assignTerm m (telToArgs tel) (Level $ Max [])
           ) $ {- else -} dontExpand
          _ -> dontExpand

-- | Eta expand blocking metavariables of record type, and reduce the
-- blocked thing.

etaExpandBlocked :: Reduce t => Blocked t -> TCM (Blocked t)
etaExpandBlocked t@NotBlocked{} = return t
etaExpandBlocked (Blocked m t)  = do
  etaExpandMeta [Records] m
  t <- reduceB t
  case t of
    Blocked m' _ | m /= m' -> etaExpandBlocked t
    _                      -> return t

-- * Solve constraint @x vs = v@.

-- | Assign to an open metavar which may not be frozen.
--   First check that metavar args are in pattern fragment.
--     Then do extended occurs check on given thing.
--
--   Assignment is aborted by throwing a @PatternErr@ via a call to
--   @patternViolation@.  This error is caught by @catchConstraint@
--   during equality checking (@compareAtom@) and leads to
--   restoration of the original constraints.

assignV :: CompareDirection -> MetaId -> Args -> Term -> TCM ()
assignV dir x args v = assignWrapper dir x (map Apply args) v $ assign dir x args v

assignWrapper :: CompareDirection -> MetaId -> Elims -> Term -> TCM () -> TCM ()
assignWrapper dir x es v doAssign = do
  ifNotM (asksTC envAssignMetas) patternViolation $ {- else -} do
    reportSDoc "tc.meta.assign" 10 $ do
      "term" <+> prettyTCM (MetaV x es) <+> text (":" ++ show dir) <+> prettyTCM v
    liftTCM $ nowSolvingConstraints doAssign `finally` solveAwakeConstraints


-- | Miller pattern unification:
--
--   @assign x vs v@ solves problem @x vs = v@ for meta @x@
--   if @vs@ are distinct variables (linearity check)
--   and @v@ depends only on these variables
--   and does not contain @x@ itself (occurs check).
--
--   This is the basic story, but we have added some features:
--
--   1. Pruning.
--   2. Benign cases of non-linearity.
--   3. @vs@ may contain record patterns.
--
--   For a reference to some of these extensions, read
--   Andreas Abel and Brigitte Pientka's TLCA 2011 paper.

assign :: CompareDirection -> MetaId -> Args -> Term -> TCM ()
assign dir x args v = do

  mvar <- lookupMeta x  -- information associated with meta x
  let t = jMetaType $ mvJudgement mvar

  -- Andreas, 2011-05-20 TODO!
  -- full normalization  (which also happens during occurs check)
  -- is too expensive! (see Issue 415)
  -- need to do something cheaper, especially if
  -- we are dealing with a Miller pattern that can be solved
  -- immediately!
  -- Ulf, 2011-08-25 DONE!
  -- Just instantiating the top-level meta, which is cheaper. The occurs
  -- check will first try without unfolding any definitions (treating
  -- arguments to definitions as flexible), if that fails it tries again
  -- with full unfolding.
  v <- instantiate v
  reportSDoc "tc.meta.assign" 45 $
    "MetaVars.assign: assigning to " <+> prettyTCM v

  reportSLn "tc.meta.assign" 75 $
    "MetaVars.assign: assigning meta  " ++ show x ++ "  with args  " ++ show args ++ "  to  " ++ show v

  case (v, mvJudgement mvar) of
      (Sort s, HasType{}) -> hasBiggerSort s
      _                   -> return ()

  -- We don't instantiate frozen mvars
  when (mvFrozen mvar == Frozen) $ do
    reportSLn "tc.meta.assign" 25 $ "aborting: meta is frozen!"
    patternViolation

  -- We never get blocked terms here anymore. TODO: we actually do. why?
  whenM (isBlockedTerm x) $ do
    reportSLn "tc.meta.assign" 25 $ "aborting: meta is a blocked term!"
    patternViolation

  -- Andreas, 2010-10-15 I want to see whether rhs is blocked
  reportSLn "tc.meta.assign" 50 $ "MetaVars.assign: I want to see whether rhs is blocked"
  reportSDoc "tc.meta.assign" 25 $ do
    v0 <- reduceB v
    case v0 of
      Blocked m0 _ -> "r.h.s. blocked on:" <+> prettyTCM m0
      NotBlocked{} -> "r.h.s. not blocked"

  -- Turn the assignment problem @_X args >= SizeLt u@ into
  -- @_X args = SizeLt (_Y args@ and constraint
  -- @_Y args >= u@.
  subtypingForSizeLt dir x mvar t args v $ \ v -> do

    -- Normalise and eta contract the arguments to the meta. These are
    -- usually small, and simplifying might let us instantiate more metas.

    -- MOVED TO expandProjectedVars:
    -- args <- etaContract =<< normalise args

    -- Also, try to expand away projected vars in meta args.
    reportSDoc "tc.meta.assign.proj" 45 $ do
      cxt <- getContextTelescope
      vcat
        [ "context before projection expansion"
        , nest 2 $ inTopContext $ prettyTCM cxt
        ]

    expandProjectedVars args v $ \ args v -> do

      reportSDoc "tc.meta.assign.proj" 45 $ do
        cxt <- getContextTelescope
        vcat
          [ "context after projection expansion"
          , nest 2 $ inTopContext $ prettyTCM cxt
          ]

      -- If we had the type here we could save the work we put
      -- into expanding projected variables.
      -- catchConstraint (ValueCmp CmpEq ? (MetaV m $ map Apply args) v) $ do

      -- Andreas, 2011-04-21 do the occurs check first
      -- e.g. _1 x (suc x) = suc (_2 x y)
      -- even though the lhs is not a pattern, we can prune the y from _2

      (relVL, nonstrictVL, irrVL) <- do
        -- Andreas, 2016-11-03 #2211 attempt to do s.th. for unused
        if False -- irrelevant $ getMetaRelevance mvar
          then do
            reportSDoc "tc.meta.assign" 25 $ "meta is irrelevant or unused"
            return (Set.toList $ allFreeVars args, empty, empty)
          else do
            let vars  = allFreeVarsWithOcc args
                relVL       = IntMap.keys $ IntMap.filter isRelevant vars
                nonstrictVL = IntMap.keys $ IntMap.filter isNonStrict vars
            -- Andreas, 2011-10-06 only irrelevant vars that are direct
            -- arguments to the meta, hence, can be abstracted over, may
            -- appear on the rhs.  (test/fail/Issue483b)
            -- Update 2011-03-27: Also irr. vars under record constructors.
            let fromIrrVar (Var i [])   = return [i]
                fromIrrVar (Con c _ vs)   =
                  ifM (isNothing <$> isRecordConstructor (conName c)) (return []) $
                    concat <$> mapM (fromIrrVar . {- stripDontCare .-} unArg) (fromMaybe __IMPOSSIBLE__ (allApplyElims vs))
                fromIrrVar _ = return []
            irrVL <- concat <$> mapM fromIrrVar
                       [ v | Arg info v <- args, isIrrelevant info ]
                          -- irrelevant (getRelevance info) ]
            return (relVL, nonstrictVL, irrVL)
      reportSDoc "tc.meta.assign" 20 $
          let pr (Var n []) = text (show n)
              pr (Def c []) = prettyTCM c
              pr _          = ".."
          in vcat
               [ "mvar args:" <+> sep (map (pr . unArg) args)
               , "fvars lhs (rel):" <+> sep (map (text . show) relVL)
               , "fvars lhs (nonstrict):" <+> sep (map (text . show) nonstrictVL)
               , "fvars lhs (irr):" <+> sep (map (text . show) irrVL)
               ]

      -- Check that the x doesn't occur in the right hand side.
      -- Prune mvars on rhs such that they can only depend on lhs vars.
      -- Herein, distinguish relevant and irrelevant vars,
      -- since when abstracting irrelevant lhs vars, they may only occur
      -- irrelevantly on rhs.
      v <- liftTCM $ occursCheck x (relVL, nonstrictVL, irrVL) v

      reportSLn "tc.meta.assign" 15 "passed occursCheck"
      verboseS "tc.meta.assign" 30 $ do
        let n = termSize v
        when (n > 200) $ reportSDoc "tc.meta.assign" 30 $
          sep [ "size" <+> text (show n)
--              , nest 2 $ "type" <+> prettyTCM t
              , nest 2 $ "term" <+> prettyTCM v
              ]

      -- Check linearity of @ids@
      -- Andreas, 2010-09-24: Herein, ignore the variables which are not
      -- free in v
      -- Ulf, 2011-09-22: we need to respect irrelevant vars as well, otherwise
      -- we'll build solutions where the irrelevant terms are not valid
      let fvs = allFreeVars v
      reportSDoc "tc.meta.assign" 20 $
        "fvars rhs:" <+> sep (map (text . show) $ Set.toList fvs)

      -- Check that the arguments are variables
      mids <- do
        res <- runExceptT $ inverseSubst args
        case res of
          -- all args are variables
          Right ids -> do
            reportSDoc "tc.meta.assign" 50 $
              "inverseSubst returns:" <+> sep (map prettyTCM ids)
            return $ Just ids
          -- we have proper values as arguments which could be cased on
          -- here, we cannot prune, since offending vars could be eliminated
          Left CantInvert  -> return Nothing
          -- we have non-variables, but these are not eliminateable
          Left NeutralArg  -> Just <$> attemptPruning x args fvs
          -- we have a projected variable which could not be eta-expanded away:
          -- same as neutral
          Left ProjectedVar{} -> Just <$> attemptPruning x args fvs

      case mids of
        Nothing  -> patternViolation -- Ulf 2014-07-13: actually not needed after all: attemptInertRHSImprovement x args v
        Just ids -> do
          -- Check linearity
          ids <- do
            res <- runExceptT $ checkLinearity {- (`Set.member` fvs) -} ids
            case res of
              -- case: linear
              Right ids -> return ids
              -- case: non-linear variables that could possibly be pruned
              Left ()   -> attemptPruning x args fvs

          -- Solve.
          m <- getContextSize
          assignMeta' m x t (length args) ids v
  where
    -- | Try to remove meta arguments from lhs that mention variables not occurring on rhs.
    attemptPruning
      :: MetaId  -- ^ Meta-variable (lhs)
      -> Args    -- ^ Meta arguments (lhs)
      -> FVs     -- ^ Variables occuring on the rhs
      -> TCM a
    attemptPruning x args fvs = do
      -- non-linear lhs: we cannot solve, but prune
      killResult <- prune x args $ Set.toList fvs
      reportSDoc "tc.meta.assign" 10 $
        "pruning" <+> prettyTCM x <+> do
        text $
          if killResult `elem` [PrunedSomething,PrunedEverything] then "succeeded"
           else "failed"
      patternViolation

{- UNUSED
-- | When faced with @_X us == D vs@ for an inert D we can solve this by
--   @_X xs := D _Ys@ with new constraints @_Yi us == vi@. This is important
--   for instance arguments, where knowing the head D might enable progress.
attemptInertRHSImprovement :: MetaId -> Args -> Term -> TCM ()
attemptInertRHSImprovement m args v = do
  reportSDoc "tc.meta.inert" 30 $ vcat
    [ "attempting inert rhs improvement"
    , nest 2 $ sep [ prettyTCM (MetaV m $ map Apply args) <+> "=="
                   , prettyTCM v ] ]
  -- Check that the right-hand side has the form D vs, for some inert constant D.
  -- Returns the type of D and a function to build an application of D.
  (a, mkRHS) <- ensureInert v
  -- Check that all arguments to the meta are neutral and does not have head D.
  -- If there are non-neutral arguments there could be solutions to the meta
  -- that computes over these arguments. If D is an argument to the meta we get
  -- multiple solutions (for instance: _M Nat == Nat can be solved by both
  -- _M := \ x -> x and _M := \ x -> Nat).
  mapM_ (ensureNeutral (mkRHS []) . unArg) args
  tel <- theTel <$> (telView =<< getMetaType m)
  -- When attempting shortcut meta solutions, metas aren't necessarily fully
  -- eta expanded. If this is the case we skip inert improvement.
  when (length args < size tel) $ do
    reportSDoc "tc.meta.inert" 30 $ "not fully applied"
    patternViolation
  -- Solve the meta with _M := \ xs -> D (_Y1 xs) .. (_Yn xs), for fresh metas
  -- _Yi.
  metaArgs <- inTopContext $ addContext tel $ newArgsMeta a
  let varArgs = map Apply $ reverse $ zipWith (\i a -> var i <$ a) [0..] (reverse args)
      sol     = mkRHS metaArgs
      argTel  = map ("x" <$) args
  reportSDoc "tc.meta.inert" 30 $ nest 2 $ vcat
    [ "a       =" <+> prettyTCM a
    , "tel     =" <+> prettyTCM tel
    , "metas   =" <+> prettyList (map prettyTCM metaArgs)
    , "sol     =" <+> prettyTCM sol
    ]
  assignTerm m argTel sol
  patternViolation  -- throwing a pattern violation here lets the constraint
                    -- machinery worry about restarting the comparison.
  where
    ensureInert :: Term -> TCM (Type, Args -> Term)
    ensureInert v = do
      let notInert = do
            reportSDoc "tc.meta.inert" 30 $ nest 2 $ "not inert:" <+> prettyTCM v
            patternViolation
          toArgs elims =
            case allApplyElims elims of
              Nothing -> do
                reportSDoc "tc.meta.inert" 30 $ nest 2 $ "can't do projections from inert"
                patternViolation
              Just args -> return args
      case v of
        Var x elims -> (, Var x . map Apply) <$> typeOfBV x
        Con c ci args  -> notInert -- (, Con c ci) <$> defType <$> getConstInfo (conName c)
        Def f elims -> do
          def <- getConstInfo f
          let good = return (defType def, Def f . map Apply)
          case theDef def of
            Axiom{}       -> good
            Datatype{}    -> good
            Record{}      -> good
            Function{}    -> notInert
            Primitive{}   -> notInert
            Constructor{} -> __IMPOSSIBLE__

        Pi{}       -> notInert -- this is actually inert but improving doesn't buy us anything for Pi
        Lam{}      -> notInert
        Sort{}     -> notInert
        Lit{}      -> notInert
        Level{}    -> notInert
        MetaV{}    -> notInert
        DontCare{} -> notInert

    ensureNeutral :: Term -> Term -> TCM ()
    ensureNeutral rhs v = do
      b <- reduceB v
      let notNeutral v = do
            reportSDoc "tc.meta.inert" 30 $ nest 2 $ "not neutral:" <+> prettyTCM v
            patternViolation
          checkRHS arg
            | arg == rhs = do
              reportSDoc "tc.meta.inert" 30 $ nest 2 $ "argument shares head with RHS:" <+> prettyTCM arg
              patternViolation
            | otherwise  = return ()
      case b of
        Blocked{}      -> notNeutral v
        NotBlocked r v ->                      -- Andrea(s) 2014-12-06 can r be useful?
          case v of
            Var x _    -> checkRHS (Var x [])
            Def f _    -> checkRHS (Def f [])
            Pi{}       -> return ()
            Sort{}     -> return ()
            Level{}    -> return ()
            Lit{}      -> notNeutral v
            DontCare{} -> notNeutral v
            MetaV{}    -> notNeutral v
            Con{}      -> notNeutral v
            Lam{}      -> notNeutral v
-- END UNUSED -}

-- | @assignMeta m x t ids u@ solves @x ids = u@ for meta @x@ of type @t@,
--   where term @u@ lives in a context of length @m@.
--   Precondition: @ids@ is linear.
assignMeta :: Int -> MetaId -> Type -> [Int] -> Term -> TCM ()
assignMeta m x t ids v = do
  let n    = length ids
      cand = List.sort $ zip ids $ map var $ downFrom n
  assignMeta' m x t n cand v

-- | @assignMeta' m x t ids u@ solves @x = [ids]u@ for meta @x@ of type @t@,
--   where term @u@ lives in a context of length @m@,
--   and @ids@ is a partial substitution.
assignMeta' :: Int -> MetaId -> Type -> Int -> SubstCand -> Term -> TCM ()
assignMeta' m x t n ids v = do
  -- we are linear, so we can solve!
  reportSDoc "tc.meta.assign" 25 $
      "preparing to instantiate: " <+> prettyTCM v

  -- Rename the variables in v to make it suitable for abstraction over ids.
  v' <- do
    -- Basically, if
    --   Γ   = a b c d e
    --   ids = d b e
    -- then
    --   v' = (λ a b c d e. v) _ 1 _ 2 0
    --
    -- Andreas, 2013-10-25 Solve using substitutions:
    -- Convert assocList @ids@ (which is sorted) into substitution,
    -- filling in __IMPOSSIBLE__ for the missing terms, e.g.
    -- [(0,0),(1,2),(3,1)] --> [0, 2, __IMP__, 1, __IMP__]
    -- ALT 1: O(m * size ids), serves as specification
    -- let ivs = [fromMaybe __IMPOSSIBLE__ $ lookup i ids | i <- [0..m-1]]
    -- ALT 2: O(m)
    let assocToList i l = case l of
          _           | i >= m -> []
          ((j,u) : l) | i == j -> Just u  : assocToList (i+1) l
          _                    -> Nothing : assocToList (i+1) l
        ivs = assocToList 0 ids
        rho = prependS __IMPOSSIBLE__ ivs $ raiseS n
    return $ applySubst rho v

  -- Metas are top-level so we do the assignment at top-level.
  inTopContext $ do
    -- Andreas, 2011-04-18 to work with irrelevant parameters
    -- we need to construct tel' from the type of the meta variable
    -- (no longer from ids which may not be the complete variable list
    -- any more)
    reportSDoc "tc.meta.assign" 15 $ "type of meta =" <+> prettyTCM t
    reportSDoc "tc.meta.assign" 70 $ "type of meta =" <+> text (show t)

    (telv@(TelV tel' a),bs) <- telViewUpToPathBoundary n t
    reportSDoc "tc.meta.assign" 30 $ "tel'  =" <+> prettyTCM tel'
    reportSDoc "tc.meta.assign" 30 $ "#args =" <+> text (show n)
    -- Andreas, 2013-09-17 (AIM XVIII): if t does not provide enough
    -- types for the arguments, it might be blocked by a meta;
    -- then we give up. (Issue 903)
    when (size tel' < n)
       patternViolation -- WAS: __IMPOSSIBLE__

    -- Perform the assignment (and wake constraints).

    let vsol = abstract tel' v'

    -- Andreas, 2013-10-25 double check solution before assigning
    whenM (optDoubleCheck <$> pragmaOptions) $ noConstraints $ dontAssignMetas $ do
      m <- lookupMeta x
      reportSDoc "tc.meta.check" 30 $ "double checking solution"
      addContext tel' $ case mvJudgement m of
        HasType{} -> do
          reportSDoc "tc.meta.check" 30 $ nest 2 $
            prettyTCM v' <+> " : " <+> prettyTCM a
          checkInternal v' a
        IsSort{}  -> void $ do
          reportSDoc "tc.meta.check" 30 $ nest 2 $
            prettyTCM v' <+> " is a sort"
          checkSort defaultAction =<< shouldBeSort (El __DUMMY_SORT__ v')

    reportSDoc "tc.meta.assign" 10 $
      "solving" <+> prettyTCM x <+> ":=" <+> prettyTCM vsol

    v' <- blockOnBoundary telv bs v'

    assignTerm x (telToArgs tel') v'
  where
    blockOnBoundary :: TelView -> Boundary -> Term -> TCM Term
    blockOnBoundary telv         [] v = return v
    blockOnBoundary (TelV tel t) bs v = addContext tel $
      blockTerm t $ do
        neg <- primINeg
        forM_ bs $ \ (r,(x,y)) -> do
          equalTermOnFace (neg `apply1` r) t x v
          equalTermOnFace r  t y v
        return v

-- | Turn the assignment problem @_X args <= SizeLt u@ into
-- @_X args = SizeLt (_Y args)@ and constraint
-- @_Y args <= u@.
subtypingForSizeLt
  :: CompareDirection -- ^ @dir@
  -> MetaId           -- ^ The meta variable @x@.
  -> MetaVariable     -- ^ Its associated information @mvar <- lookupMeta x@.
  -> Type             -- ^ Its type @t = jMetaType $ mvJudgement mvar@
  -> Args             -- ^ Its arguments.
  -> Term             -- ^ Its to-be-assigned value @v@, such that @x args `dir` v@.
  -> (Term -> TCM ()) -- ^ Continuation taking its possibly assigned value.
  -> TCM ()
subtypingForSizeLt DirEq x mvar t args v cont = cont v
subtypingForSizeLt dir   x mvar t args v cont = do
  let fallback = cont v
  -- Check whether we have built-ins SIZE and SIZELT
  (mSize, mSizeLt) <- getBuiltinSize
  caseMaybe mSize   fallback $ \ qSize   -> do
    caseMaybe mSizeLt fallback $ \ qSizeLt -> do
      -- Check whether v is a SIZELT
      v <- reduce v
      case v of
        Def q [Apply (Arg ai u)] | q == qSizeLt -> do
          -- Clone the meta into a new size meta @y@.
          -- To this end, we swap the target of t for Size.
          TelV tel _ <- telView t
          let size = sizeType_ qSize
              t'   = telePi tel size
          y <- newMeta (mvInfo mvar) (mvPriority mvar) (mvPermutation mvar)
                       (HasType __IMPOSSIBLE__ t')
          -- Note: no eta-expansion of new meta possible/necessary.
          -- Add the size constraint @y args `dir` u@.
          let yArgs = MetaV y $ map Apply args
          addConstraint $ dirToCmp (`ValueCmp` size) dir yArgs u
          -- We continue with the new assignment problem, and install
          -- an exception handler, since we created a meta and a constraint,
          -- so we cannot fall back to the original handler.
          let xArgs = MetaV x $ map Apply args
              v'    = Def qSizeLt [Apply $ Arg ai yArgs]
              c     = dirToCmp (`ValueCmp` sizeUniv) dir xArgs v'
          catchConstraint c $ cont v'
        _ -> fallback

-- | Eta-expand bound variables like @z@ in @X (fst z)@.
expandProjectedVars
  :: ( Show a, PrettyTCM a, NoProjectedVar a
     -- , Normalise a, TermLike a, Subst Term a
     , ReduceAndEtaContract a
     , PrettyTCM b, Subst Term b
     )
  => a  -- ^ Meta variable arguments.
  -> b  -- ^ Right hand side.
  -> (a -> b -> TCM c)
  -> TCM c
expandProjectedVars args v ret = loop (args, v) where
  loop (args, v) = do
    reportSDoc "tc.meta.assign.proj" 45 $ "meta args: " <+> prettyTCM args
    args <- callByName $ reduceAndEtaContract args
    -- args <- etaContract =<< normalise args
    reportSDoc "tc.meta.assign.proj" 45 $ "norm args: " <+> prettyTCM args
    reportSDoc "tc.meta.assign.proj" 85 $ "norm args: " <+> text (show args)
    let done = ret args v
    case noProjectedVar args of
      Right ()              -> do
        reportSDoc "tc.meta.assign.proj" 40 $
          "no projected var found in args: " <+> prettyTCM args
        done
      Left (ProjVarExc i _) -> etaExpandProjectedVar i (args, v) done loop

-- | Eta-expand a de Bruijn index of record type in context and passed term(s).
etaExpandProjectedVar :: (PrettyTCM a, Subst Term a) => Int -> a -> TCM c -> (a -> TCM c) -> TCM c
etaExpandProjectedVar i v fail succeed = do
  reportSDoc "tc.meta.assign.proj" 40 $
    "trying to expand projected variable" <+> prettyTCM (var i)
  caseMaybeM (etaExpandBoundVar i) fail $ \ (delta, sigma, tau) -> do
    reportSDoc "tc.meta.assign.proj" 25 $
      "eta-expanding var " <+> prettyTCM (var i) <+>
      " in terms " <+> prettyTCM v
    inTopContext $ addContext delta $
      succeed $ applySubst tau v

-- | Check whether one of the meta args is a projected var.
class NoProjectedVar a where
  noProjectedVar :: a -> Either ProjVarExc ()

data ProjVarExc = ProjVarExc Int [(ProjOrigin, QName)]

instance NoProjectedVar Term where
  noProjectedVar t =
    case t of
      Var i es
        | qs@(_:_) <- takeWhileJust id $ map isProjElim es -> Left $ ProjVarExc i qs
      -- Andreas, 2015-09-12 Issue #1316:
      -- Also look in inductive record constructors
      Con (ConHead _ Inductive (_:_)) _ es | Just vs <- allApplyElims es -> noProjectedVar vs
      _ -> return ()

instance NoProjectedVar a => NoProjectedVar (Arg a) where
  noProjectedVar = Fold.mapM_ noProjectedVar

instance NoProjectedVar a => NoProjectedVar [a] where
  noProjectedVar = Fold.mapM_ noProjectedVar


-- | Normalize just far enough to be able to eta-contract maximally.
class (TermLike a, Subst Term a, Reduce a) => ReduceAndEtaContract a where
  reduceAndEtaContract :: a -> TCM a

  default reduceAndEtaContract
    :: (Traversable f, TermLike b, Subst Term b, Reduce b, ReduceAndEtaContract b, f b ~ a)
    => a -> TCM a
  reduceAndEtaContract = Trav.mapM reduceAndEtaContract

instance ReduceAndEtaContract a => ReduceAndEtaContract [a] where
instance ReduceAndEtaContract a => ReduceAndEtaContract (Arg a) where

instance ReduceAndEtaContract Term where
  reduceAndEtaContract u = do
    reduce u >>= \case
      -- In case of lambda or record constructor, it makes sense to
      -- reduce further.
      Lam ai (Abs x b) -> etaLam ai x =<< reduceAndEtaContract b
      Con c ci es -> etaCon c ci es $ \ r c ci args -> do
        args <- reduceAndEtaContract args
        etaContractRecord r c ci args
      v -> return v

{- UNUSED, BUT KEEP!
-- Wrong attempt at expanding bound variables.
-- The following code curries meta instead.

-- | @etaExpandProjectedVar mvar x t n qs@
--
--   @mvar@ is the meta var info.
--   @x@ is the meta variable we are trying to solve for.
--   @t@ is its type.
--   @n@ is the number of the meta arg we want to curry (starting at 0).
--   @qs@ is the projection path along which we curry.
--
etaExpandProjectedVar :: MetaVariable -> MetaId -> Type -> Int -> [QName] -> TCM a
etaExpandProjectedVar mvar x t n qs = inTopContext $ do
  (_, uncurry, t') <- curryAt t n
  let TelV tel a = telView' t'
      perm       = idP (size tel)
  y <- newMeta (mvInfo mvar) (mvPriority mvar) perm (HasType __IMPOSSIBLE__ t')
  assignTerm' x (uncurry $ MetaV y [])
  patternViolation
-}

{-
  -- first, strip the leading n domains (which remain unchanged)
  TelV gamma core <- telViewUpTo n t
  case unEl core of
    -- There should be at least one domain left
    Pi (Dom ai a) b -> do
      -- Eta-expand @dom@ along @qs@ into a telescope @tel@, computing a substitution.
      -- For now, we only eta-expand once.
      -- This might trigger another call to @etaExpandProjectedVar@ later.
      -- A more efficient version does all the eta-expansions at once here.
      (r, pars, def) <- fromMaybe __IMPOSSIBLE__ <$> isRecordType a
      unless (recEtaEquality def) __IMPOSSIBLE__
      let tel = recTel def `apply` pars
          m   = size tel
          v   = Con (recConHead def) $ map var $ downFrom m
          b'  = raise m b `absApp` v
          fs  = recFields def
          vs  = zipWith (\ f i -> Var i [Proj f]) fs $ downFrom m
          -- v = c (n-1) ... 1 0
      (tel, u) <- etaExpandAtRecordType a $ var 0
      -- TODO: compose argInfo ai with tel.
      -- Substitute into @b@.
      -- Abstract over @tel@.
      -- Abstract over @gamma@.
      -- Create new meta.
      -- Solve old meta, using substitution.
      patternViolation
    _ -> __IMPOSSIBLE__
-}

type FVs = Set.VarSet
type SubstCand = [(Int,Term)] -- ^ a possibly non-deterministic substitution

-- | Turn non-det substitution into proper substitution, if possible.
--   Otherwise, raise the error.
checkLinearity :: SubstCand -> ExceptT () TCM SubstCand
checkLinearity ids0 = do
  let ids = List.sortBy (compare `on` fst) ids0  -- see issue 920
  let grps = groupOn fst ids
  concat <$> mapM makeLinear grps
  where
    -- | Non-determinism can be healed if type is singleton. [Issue 593]
    --   (Same as for irrelevance.)
    makeLinear :: SubstCand -> ExceptT () TCM SubstCand
    makeLinear []            = __IMPOSSIBLE__
    makeLinear grp@[_]       = return grp
    makeLinear (p@(i,t) : _) =
      ifM ((Right True ==) <$> do isSingletonTypeModuloRelevance =<< typeOfBV i)
        (return [p])
        (throwError ())

-- Intermediate result in the following function
type Res = [(Arg Nat, Term)]

-- | Exceptions raised when substitution cannot be inverted.
data InvertExcept
  = CantInvert                -- ^ Cannot recover.
  | NeutralArg                -- ^ A potentially neutral arg: can't invert, but can try pruning.
  | ProjectedVar Int [(ProjOrigin, QName)]  -- ^ Try to eta-expand var to remove projs.

-- | Check that arguments @args@ to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf and eta-reduced.
--   Parameters are represented as @Var@s so @checkArgs@ really
--   checks that all args are @Var@s and returns the "substitution"
--   to be applied to the rhs of the equation to solve.
--   (If @args@ is considered a substitution, its inverse is returned.)
--
--   The returned list might not be ordered.
--   Linearity, i.e., whether the substitution is deterministic,
--   has to be checked separately.
--
inverseSubst :: Args -> ExceptT InvertExcept TCM SubstCand
inverseSubst args = map (mapFst unArg) <$> loop (zip args terms)
  where
    loop  = foldM isVarOrIrrelevant []
    terms = map var (downFrom (size args))
    failure = do
      lift $ reportSDoc "tc.meta.assign" 15 $ vcat
        [ "not all arguments are variables: " <+> prettyTCM args
        , "  aborting assignment" ]
      throwError CantInvert
    neutralArg = throwError NeutralArg

    isVarOrIrrelevant :: Res -> (Arg Term, Term) -> ExceptT InvertExcept TCM Res
    isVarOrIrrelevant vars (arg, t) =
      case arg of
        -- i := x
        Arg info (Var i []) -> return $ (Arg info i, t) `cons` vars

        -- π i := x  try to eta-expand projection π away!
        Arg _ (Var i es) | Just qs <- mapM isProjElim es ->
          throwError $ ProjectedVar i qs

        -- (i, j) := x  becomes  [i := fst x, j := snd x]
        -- Andreas, 2013-09-17 but only if constructor is fully applied
        Arg info (Con c ci es) -> do
          let fallback
               | isIrrelevant info = return vars
               | otherwise                              = failure
          isRC <- lift $ isRecordConstructor $ conName c
          case isRC of
            Just (_, Record{ recFields = fs })
              | length fs == length es -> do
                let aux (Arg _ v) (Arg info' f) = (Arg ai v,) $ t `applyE` [Proj ProjSystem f] where
                     ai = ArgInfo
                       { argInfoHiding   = min (getHiding info) (getHiding info')
                       , argInfoModality = Modality
                         { modRelevance  = max (getRelevance info) (getRelevance info')
                         , modQuantity   = max (getQuantity  info) (getQuantity  info')
                         }
                       , argInfoOrigin   = min (getOrigin info) (getOrigin info')
                       , argInfoFreeVariables = unknownFreeVariables
                       }
                    vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                res <- loop $ zipWith aux vs fs
                return $ res `append` vars
              | otherwise -> fallback
            Just _  -> __IMPOSSIBLE__
            Nothing -> fallback

        -- An irrelevant argument which is not an irrefutable pattern is dropped
        Arg info _ | isIrrelevant info -> return vars
        -- Andreas, 2013-10-29
        -- An irrelevant part can also be marked by a DontCare
        -- (coming from an irrelevant projection), see Issue 927:
        Arg _ DontCare{}                                    -> return vars

        -- Distinguish args that can be eliminated (Con,Lit,Lam,unsure) ==> failure
        -- from those that can only put somewhere as a whole ==> neutralArg
        Arg _ Var{}      -> neutralArg
        Arg _ Def{}      -> neutralArg  -- Note that this Def{} is in normal form and might be prunable.
        Arg _ Lam{}      -> failure
        Arg _ Lit{}      -> failure
        Arg _ MetaV{}    -> failure
        Arg _ Pi{}       -> neutralArg
        Arg _ Sort{}     -> neutralArg
        Arg _ Level{}    -> neutralArg
        Arg _ (Dummy s)  -> __IMPOSSIBLE_VERBOSE__ s

    -- managing an assoc list where duplicate indizes cannot be irrelevant vars
    append :: Res -> Res -> Res
    append res vars = foldr cons vars res

    -- adding an irrelevant entry only if not present
    cons :: (Arg Nat, Term) -> Res -> Res
    cons a@(Arg ai i, t) vars
      | isIrrelevant ai = applyUnless (any ((i==) . unArg . fst) vars) (a :) vars
      | otherwise       = a :  -- adding a relevant entry
          -- filter out duplicate irrelevants
          filter (not . (\ a@(Arg info j, t) -> isIrrelevant info && i == j)) vars

-- UNUSED
-- -- | Used in 'Agda.Interaction.BasicOps.giveExpr'.
-- updateMeta :: MetaId -> Term -> TCM ()
-- updateMeta mI v = do
--     mv <- lookupMeta mI
--     withMetaInfo' mv $ do
--       args <- getContextArgs
--       noConstraints $ assignV DirEq mI args v

-- | Turn open metas into postulates.
--
--   Preconditions:
--
--   1. We are 'inTopContext'.
--
--   2. 'envCurrentModule' is set to the top-level module.
--
openMetasToPostulates :: TCM ()
openMetasToPostulates = do
  m <- asksTC envCurrentModule

  -- Go through all open metas.
  ms <- IntMap.assocs <$> useTC stMetaStore
  forM_ ms $ \ (x, mv) -> do
    when (isOpenMeta $ mvInstantiation mv) $ do
      let t = jMetaType $ mvJudgement mv

      -- Create a name for the new postulate.
      let r = clValue $ miClosRange $ mvInfo mv
      -- s <- render <$> prettyTCM x -- Using _ is a bad idea, as it prints as prefix op
      let s = "unsolved#meta." ++ show x
      n <- freshName r s
      let q = A.QName m n

      -- Debug.
      reportSDoc "meta.postulate" 20 $ vcat
        [ text ("Turning " ++ if isSortMeta_ mv then "sort" else "value" ++ " meta ")
            <+> prettyTCM (MetaId x) <+> " into postulate."
        , nest 2 $ vcat
          [ "Name: " <+> prettyTCM q
          , "Type: " <+> prettyTCM t
          ]
        ]

      -- Add the new postulate to the signature.
      addConstant q $ defaultDefn defaultArgInfo q t Axiom

      -- Solve the meta.
      let inst = InstV [] $ Def q []
      updateMetaVar (MetaId x) $ \ mv0 -> mv0 { mvInstantiation = inst }
      return ()
