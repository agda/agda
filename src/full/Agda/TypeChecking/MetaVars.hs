{-# LANGUAGE CPP, RelaxedPolyRec, GeneralizedNewtypeDeriving #-}

module Agda.TypeChecking.MetaVars where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import Data.Generics
import Data.List as List hiding (sort)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Agda.Utils.IO.Locale as LocIO

import Agda.Syntax.Common
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Literal
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Free
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.EtaContract

import Agda.TypeChecking.MetaVars.Occurs

import {-# SOURCE #-} Agda.TypeChecking.Conversion -- SOURCE NECESSARY

import Agda.Utils.Fresh
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation
import qualified Agda.Utils.VarSet as Set

import Agda.TypeChecking.Monad.Debug

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Find position of a value in a list.
--   Used to change metavar argument indices during assignment.
--
--   @reverse@ is necessary because we are directly abstracting over the list.
--
findIdx :: Eq a => [a] -> a -> Maybe Int
findIdx vs v = findIndex (==v) (reverse vs)

-- | Check whether a meta variable is a place holder for a blocked term.
isBlockedTerm :: MetaId -> TCM Bool
isBlockedTerm x = do
    reportSLn "tc.meta.blocked" 12 $ "is " ++ show x ++ " a blocked term? "
    i <- mvInstantiation <$> lookupMeta x
    let r = case i of
	    BlockedConst{}                 -> True
            PostponedTypeCheckingProblem{} -> True
	    InstV{}                        -> False
	    InstS{}                        -> False
	    Open{}                         -> False
	    OpenIFS{}                      -> False
    reportSLn "tc.meta.blocked" 12 $
      if r then "  yes, because " ++ show i else "  no"
    return r

isEtaExpandable :: MetaId -> TCM Bool
isEtaExpandable x = do
    i <- mvInstantiation <$> lookupMeta x
    return $ case i of
      Open{}                         -> True
      OpenIFS{}                      -> False
      InstV{}                        -> False
      InstS{}                        -> False
      BlockedConst{}                 -> False
      PostponedTypeCheckingProblem{} -> False

-- * Performing the assignment

-- | Performing the meta variable assignment.
--
--   The instantiation should not be an 'InstV' or 'InstS' and the 'MetaId'
--   should point to something 'Open' or a 'BlockedConst'.
--   Further, the meta variable may not be 'Frozen'.
assignTerm :: MetaId -> Term -> TCM ()
assignTerm x t = do
    reportSLn "tc.meta.assign" 70 $ show x ++ " := " ++ show t
    whenM (isFrozen x) __IMPOSSIBLE__  -- verify (new) invariant
    let i = metaInstance (killRange t)
    verboseS "profile.metas" 10 $ liftTCM $ tickMax "max-open-metas" . size =<< getOpenMetas
    modifyMetaStore $ ins x i
    etaExpandListeners x
    wakeupConstraints x
    reportSLn "tc.meta.assign" 20 $ "completed assignment of " ++ show x
  where
    metaInstance = InstV
    ins x i store = Map.adjust (inst i) x store
    inst i mv = mv { mvInstantiation = i }

-- * Creating meta variables.

newSortMeta :: TCM Sort
newSortMeta =
  ifM typeInType (return $ mkType 0) $
  ifM hasUniversePolymorphism (newSortMetaCtx =<< getContextArgs)
  -- else (no universe polymorphism)
  $ do i <- createMetaInfo
       x <- newMeta i normalMetaPriority (idP 0) (IsSort () topSort)
       return $ Type $ Max [Plus 0 $ MetaLevel x []]

newSortMetaCtx :: Args -> TCM Sort
newSortMetaCtx vs =
  ifM typeInType (return $ mkType 0) $ do
    i   <- createMetaInfo
    tel <- getContextTelescope
    let t = telePi_ tel topSort
    x   <- newMeta i normalMetaPriority (idP 0) (IsSort () t)
    reportSDoc "tc.meta.new" 50 $
      text "new sort meta" <+> prettyTCM x <+> text ":" <+> prettyTCM t
    return $ Type $ Max [Plus 0 $ MetaLevel x vs]

newTypeMeta :: Sort -> TCM Type
newTypeMeta s = El s <$> newValueMeta (sort s)

newTypeMeta_ ::  TCM Type
newTypeMeta_  = newTypeMeta =<< (workOnTypes $ newSortMeta)
-- TODO: (this could be made work with new uni-poly)
-- Andreas, 2011-04-27: If a type meta gets solved, than we do not have to check
-- that it has a sort.  The sort comes from the solution.
-- newTypeMeta_  = newTypeMeta Inf

-- | Create a new "implicit from scope" metavariable
newIFSMeta ::  Type -> TCM Term
newIFSMeta t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newIFSMetaCtx (telePi_ tel t) vs

-- | Create a new value meta with specific dependencies.
newIFSMetaCtx :: Type -> Args -> TCM Term
newIFSMetaCtx t vs = do
  i <- createMetaInfo
  let TelV tel _ = telView' t
      perm = idP (size tel)
  x <- newMeta' OpenIFS i normalMetaPriority perm (HasType () t)
  reportSDoc "tc.meta.new" 50 $ fsep
    [ text "new ifs meta:"
    , nest 2 $ prettyTCM vs <+> text "|-"
    , nest 2 $ text (show x) <+> text ":" <+> prettyTCM t
    ]
  solveConstraint_ $ FindInScope x
  return (MetaV x vs)

-- | Create a new metavariable, possibly η-expanding in the process.
newValueMeta ::  Type -> TCM Term
newValueMeta t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx (telePi_ tel t) vs

newValueMetaCtx :: Type -> Args -> TCM Term
newValueMetaCtx t ctx = do
  m@(MetaV i _) <- newValueMetaCtx' t ctx
  instantiateFull m

-- | Create a new value meta without η-expanding.
newValueMeta' :: Type -> TCM Term
newValueMeta' t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx' (telePi_ tel t) vs

-- | Create a new value meta with specific dependencies.
newValueMetaCtx' :: Type -> Args -> TCM Term
newValueMetaCtx' t vs = do
  i <- createMetaInfo
  let TelV tel _ = telView' t
      perm = idP (size tel)
  x <- newMeta i normalMetaPriority perm (HasType () t)
  reportSDoc "tc.meta.new" 50 $ fsep
    [ text "new meta:"
    , nest 2 $ prettyTCM vs <+> text "|-"
    , nest 2 $ text (show x) <+> text ":" <+> prettyTCM t
    ]
  etaExpandMetaSafe x
  return $ MetaV x vs

newTelMeta :: Telescope -> TCM Args
newTelMeta tel = newArgsMeta (abstract tel $ El Prop $ Sort Prop)

newArgsMeta :: Type -> TCM Args
newArgsMeta t = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newArgsMetaCtx t tel args

newArgsMetaCtx :: Type -> Telescope -> Args -> TCM Args
newArgsMetaCtx (El s tm) tel ctx = do
  tm <- reduce tm
  case funView tm of
      FunV (Arg h r a) _  -> do
	  arg  <- (Arg h r) <$>
                   {-
                     -- Andreas, 2010-09-24 skip irrelevant record fields when eta-expanding a meta var
                     -- Andreas, 2010-10-11 this is WRONG, see Issue 347
                    if r == Irrelevant then return DontCare else
                    -}
                     newValueMetaCtx (telePi_ tel a) ctx
	  args <- newArgsMetaCtx (El s tm `piApply` [arg]) tel ctx
	  return $ arg : args
      NoFunV _    -> return []

-- | Create a metavariable of record type. This is actually one metavariable
--   for each field.
newRecordMeta :: QName -> Args -> TCM Term
newRecordMeta r pars = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newRecordMetaCtx r pars tel args

newRecordMetaCtx :: QName -> Args -> Telescope -> Args -> TCM Term
newRecordMetaCtx r pars tel ctx = do
  ftel	 <- flip apply pars <$> getRecordFieldTypes r
  fields <- newArgsMetaCtx (telePi_ ftel $ sort Prop) tel ctx
  con    <- getRecordConstructor r
  return $ Con con fields

newQuestionMark :: Type -> TCM Term
newQuestionMark t = do
  m@(MetaV x _) <- newValueMeta' t
  ii		<- fresh
  addInteractionPoint ii x
  return m

-- | Construct a blocked constant if there are constraints.
blockTerm :: Type -> TCM Term -> TCM Term
blockTerm t blocker = do
  (pid, v) <- newProblem blocker
  blockTermOnProblem t v pid

blockTermOnProblem :: Type -> Term -> ProblemId -> TCM Term
blockTermOnProblem t v pid =
  ifM (isProblemSolved pid) (return v) $ do
    i   <- createMetaInfo
    vs  <- getContextArgs
    tel <- getContextTelescope
    x   <- newMeta' (BlockedConst $ abstract tel v)
                    i lowMetaPriority (idP $ size tel)
                    (HasType () $ telePi_ tel t)
                    -- we don't instantiate blocked terms
    escapeContext (size tel) $ addConstraint (Guarded (UnBlock x) pid)
    reportSDoc "tc.meta.blocked" 20 $ vcat
      [ text "blocked" <+> prettyTCM x <+> text ":=" <+> escapeContext (size tel) (prettyTCM $ abstract tel v)
      , text "     by" <+> (prettyTCM =<< getConstraintsForProblem pid) ]
    inst <- isInstantiatedMeta x
    case inst of
      True  -> instantiate (MetaV x vs)
      False -> do
        -- We don't return the blocked term instead create a fresh metavariable
        -- that we compare against the blocked term once it's unblocked. This way
        -- blocked terms can be instantiated before they are unblocked, thus making
        -- constraint solving a bit more robust against instantiation order.
        v   <- newValueMeta t
        i   <- liftTCM (fresh :: TCM Integer)
        -- This constraint is woken up when unblocking, so it doesn't need a problem id.
        cmp <- buildProblemConstraint 0 (ValueCmp CmpEq t v (MetaV x vs))
        listenToMeta (CheckConstraint i cmp) x
        return v

-- | @unblockedTester t@ returns @False@ if @t@ is a meta or a blocked term.
--
--   Auxiliary function to create a postponed type checking problem.
unblockedTester :: Type -> TCM Bool
unblockedTester t = do
  t <- reduceB $ unEl t
  case t of
    Blocked{}          -> return False
    NotBlocked MetaV{} -> return False
    _                  -> return True

-- | Create a postponed type checking problem @e : t@ that waits for type @t@
--   to unblock (become instantiated or its constraints resolved).
postponeTypeCheckingProblem_ :: A.Expr -> Type -> TCM Term
postponeTypeCheckingProblem_ e t = do
  postponeTypeCheckingProblem e t (unblockedTester t)

-- | Create a postponed type checking problem @e : t@ that waits for conditon
--   @unblock@.  A new meta is created in the current context that has as
--   instantiation the postponed type checking problem.  An 'UnBlock' constraint
--   is added for this meta, which links to this meta.
postponeTypeCheckingProblem :: A.Expr -> Type -> TCM Bool -> TCM Term
postponeTypeCheckingProblem e t unblock = do
  i   <- createMetaInfo
  tel <- getContextTelescope
  cl  <- buildClosure (e, t, unblock)
  m   <- newMeta' (PostponedTypeCheckingProblem cl)
                  i normalMetaPriority (idP (size tel))
         $ HasType () $ telePi_ tel t
  addConstraint (UnBlock m)
  MetaV m <$> getContextArgs

-- | Eta expand metavariables listening on the current meta.
etaExpandListeners :: MetaId -> TCM ()
etaExpandListeners m = do
  ls <- getMetaListeners m
  clearMetaListeners m	-- we don't really have to do this
  mapM_ wakeupListener ls

-- | Wake up a meta listener and let it do its thing
wakeupListener :: Listener -> TCM ()
  -- Andreas 2010-10-15: do not expand record mvars, lazyness needed for irrelevance
wakeupListener (EtaExpand x)         = etaExpandMetaSafe x
wakeupListener (CheckConstraint _ c) = do
  reportSDoc "tc.meta.blocked" 20 $ text "waking boxed constraint" <+> prettyTCM c
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
  deriving (Eq, Enum, Bounded)

-- | All possible metavariable kinds.

allMetaKinds :: [MetaKind]
allMetaKinds = [minBound .. maxBound]

-- | Eta expand a metavariable, if it is of the specified kind.
--   Don't do anything if the metavariable is a blocked term.
etaExpandMeta :: [MetaKind] -> MetaId -> TCM ()
etaExpandMeta kinds m = whenM (isEtaExpandable m) $ do
  verboseBracket "tc.meta.eta" 20 ("etaExpandMeta " ++ show m) $ do
  meta       <- lookupMeta m
  let HasType _ a = mvJudgement meta
  TelV tel b <- telViewM a
  let args	 = [ Arg h r $ Var i []
		   | (i, Arg h r _) <- reverse $ zip [0..] $ reverse $ telToList tel
		   ]
  bb <- reduceB b  -- the target in the type @a@ of @m@
  case unEl <$> bb of
    -- if the target type of @m@ is a meta variable @x@ itself
    -- (@NonBlocked (MetaV{})@),
    -- or it is blocked by a meta-variable @x@ (@Blocked@), we cannot
    -- eta expand now, we have to postpone this.  Once @x@ is
    -- instantiated, we can continue eta-expanding m.  This is realized
    -- by adding @m@ to the listeners of @x@.
    Blocked x _               -> listenToMeta (EtaExpand m) x
    NotBlocked (MetaV x _)    -> listenToMeta (EtaExpand m) x
    NotBlocked lvl@(Def r ps) ->
      ifM (isEtaRecord r) (do
	let expand = do
              u <- withMetaInfo (mvInfo meta) $ newRecordMetaCtx r ps tel args
              inContext [] $ addCtxTel tel $ do
                verboseS "tc.meta.eta" 15 $ do
                  du <- prettyTCM u
                  liftIO $ LocIO.putStrLn $ "eta expanding: " ++ show m ++ " --> " ++ show du
                noConstraints $ assignV m args u  -- should never produce any constraints
        if Records `elem` kinds then
          expand
         else if SingletonRecords `elem` kinds then do
          singleton <- isSingletonRecord r ps
          case singleton of
            Left x      -> listenToMeta (EtaExpand m) x
            Right False -> return ()
            Right True  -> expand
         else
          return ()
      ) $ when (Levels `elem` kinds) $ do
        mlvl <- getBuiltin' builtinLevel
        tt   <- typeInType
        if tt && Just lvl == mlvl
         then do
          reportSLn "tc.meta.eta" 20 $ "Expanding level meta to 0 (type-in-type)"
          noConstraints $ assignV m args (Level $ Max [])
         else
          return ()
    _ -> return ()

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

assignV :: MetaId -> Args -> Term -> TCM ()
assignV x args v = do
	reportSDoc "tc.meta.assign" 10 $ do
	  text "term" <+> prettyTCM (MetaV x args) <+> text ":=" <+> prettyTCM v
        liftTCM $ nowSolvingConstraints (assign x args v) `finally` solveAwakeConstraints

-- | @assign sort? x vs v@
assign :: MetaId -> Args -> Term -> TCM ()
assign x args v = do
        mvar <- lookupMeta x  -- information associated with meta x

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
        reportSLn "tc.meta.assign" 50 $ "MetaVars.assign: assigning to " ++ show v

        case (v, mvJudgement mvar) of
            (Sort Inf, HasType{}) -> typeError $ GenericError "Setω is not a valid type."
            _                     -> return ()

        -- We don't instantiate frozen mvars
        when (mvFrozen mvar == Frozen) $ do
          reportSLn "tc.meta.assign" 25 $ "aborting: meta is frozen!"
          patternViolation

	-- We never get blocked terms here anymore. TODO: we actually do. why?
	whenM (isBlockedTerm x) patternViolation

        -- Andreas, 2010-10-15 I want to see whether rhs is blocked
        reportSLn "tc.meta.assign" 50 $ "MetaVars.assign: I want to see whether rhs is blocked"
        reportSDoc "tc.meta.assign" 25 $ do
          v0 <- reduceB v
          case v0 of
            Blocked m0 _ -> text "r.h.s. blocked on:" <+> prettyTCM m0
            NotBlocked{} -> text "r.h.s. not blocked"

        -- Normalise and eta contract the arguments to the meta. These are
        -- usually small, and simplifying might let us instantiate more metas.
        args <- etaContract =<< normalise args

        -- Andreas, 2011-04-21 do the occurs check first
        -- e.g. _1 x (suc x) = suc (_2 x y)
        -- even though the lhs is not a pattern, we can prune the y from _2
        let fvsL = Set.toList $ relevantVars $ freeVars args
        reportSDoc "tc.meta.assign" 20 $
            let pr (Var n []) = text (show n)
                pr (Def c []) = prettyTCM c
                pr _          = text ".."
            in vcat
                 [ text "mvar args:" <+> sep (map (pr . unArg) args)
                 , text "fvars lhs:" <+> sep (map (text . show) fvsL)
                 ]

	-- Check that the x doesn't occur in the right hand side
        -- Prune mvars on rhs such that they can only depend on fvsL
	v <- liftTCM $ occursCheck x fvsL v

	reportSLn "tc.meta.assign" 15 "passed occursCheck"
	verboseS "tc.meta.assign" 30 $ do
	  let n = size v
	  when (n > 200) $ do
	    d <- sep [ text "size" <+> text (show n)
--		     , nest 2 $ text "type" <+> prettyTCM t
		     , nest 2 $ text "term" <+> prettyTCM v
		     ]
	    liftIO $ LocIO.print d

	-- Check that the arguments are variables
	ids <- checkAllVars args

        -- Check linearity of @ids@
        -- Andreas, 2010-09-24: Herein, ignore the variables which are not
        -- free in v
        let fvs = relevantVars $ freeVars v
        reportSDoc "tc.meta.assign" 20 $
          text "fvars rhs:" <+> sep (map (text . show) $ Set.toList fvs)

        unless (distinct $ filter (`Set.member` fvs) ids) $ do
          -- non-linear lhs: we cannot solve, but prune
          killResult <- prune x args $ Set.toList fvs
          reportSDoc "tc.meta.assign" 10 $
            text "pruning" <+> prettyTCM x <+> (text $
              if killResult `elem` [PrunedSomething,PrunedEverything] then "succeeded"
               else "failed")
          patternViolation

{- Andreas, 2011-04-21 this does not work
        if not (distinct $ filter (`Set.member` fvs) ids) then do
          -- non-linear lhs: we cannot solve, but prune
          ok <- prune x args $ Set.toList fvs
          if ok then return [] else patternViolation

        else do
-}
        -- we are linear, so we can solve!
	reportSDoc "tc.meta.assign" 25 $
	    text "preparing to instantiate: " <+> prettyTCM v

	-- Rename the variables in v to make it suitable for abstraction over ids.
	v' <- do
	    -- Basically, if
	    --   Γ   = a b c d e
	    --   ids = d b e
	    -- then
	    --   v' = (λ a b c d e. v) _ 1 _ 2 0
	    tel   <- getContextTelescope
	    gamma <- map defaultArg <$> getContextTerms
	    let iargs = reverse $ zipWith (rename ids) [0..] $ reverse gamma
		v'    = raise (size args) (abstract tel v) `apply` iargs
	    return v'

        -- Andreas, 2011-04-18 to work with irrelevant parameters DontCare
        -- we need to construct tel' from the type of the meta variable
        -- (no longer from ids which may not be the complete variable list
        -- any more)
        let t = jMetaType $ mvJudgement mvar
	reportSDoc "tc.meta.assign" 15 $ text "type of meta =" <+> prettyTCM t
--	reportSDoc "tc.meta.assign" 30 $ text "type of meta =" <+> text (show t)

        TelV tel0 core0 <- telViewM t
        let n = length args
	reportSDoc "tc.meta.assign" 30 $ text "tel0  =" <+> prettyTCM tel0
	reportSDoc "tc.meta.assign" 30 $ text "#args =" <+> text (show n)
        when (size tel0 < n) __IMPOSSIBLE__
        let tel' = telFromList $ take n $ telToList tel0

	reportSDoc "tc.meta.assign" 10 $
	  text "solving" <+> prettyTCM x <+> text ":=" <+> prettyTCM (abstract tel' v')

	-- Perform the assignment (and wake constraints). Metas
	-- are top-level so we do the assignment at top-level.
	n <- size <$> getContextTelescope
	escapeContext n $ assignTerm x $ killRange (abstract tel' v')
	return ()
    where
        rename :: [Nat] -> Nat -> Arg Term -> Arg Term
	rename ids i arg = case findIndex (==i) ids of
	    Just j  -> fmap (const $ Var (fromIntegral j) []) arg
	    Nothing -> fmap (const __IMPOSSIBLE__) arg	-- we will end up here, but never look at the result

type FVs = Set.VarSet

-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--   Parameters are represented as @Var@s so @checkArgs@ really
--     checks that all args are @Var@s and returns the
--     list of corresponding indices for each arg.
--   Linearity has to be checked separately.
--
--   @reverse@ is necessary because we are directly abstracting over this list @ids@.
checkAllVars :: Args -> TCM [Nat]
checkAllVars args =
  case allVarOrIrrelevant args of
    Nothing -> do
      reportSDoc "tc.meta.assign" 15 $ vcat [ text "not all variables: " <+> prettyTCM args
                                            , text "  aborting assignment" ]
      patternViolation
    Just is -> return $ map unArg is

-- | filter out irrelevant args and check that all others are variables.
--   Return the reversed list of variables.
allVarOrIrrelevant :: Args -> Maybe [Arg Nat]
allVarOrIrrelevant args = foldM isVarOrIrrelevant [] args where
  isVarOrIrrelevant vars arg =
    case arg of
      Arg h r (Var i []) -> return $ Arg h r i : vars
      -- Andreas, 2011-04-27 keep irrelevant variables
      Arg h Irrelevant _ -> return $ Arg h Irrelevant (-1) : vars -- any impossible deBruijn index will do (see Jason Reed, LFMTP 09 "_" or Nipkow "minus infinity")
      _                  -> Nothing


updateMeta :: MetaId -> Term -> TCM ()
updateMeta mI v = do
    mv <- lookupMeta mI
    withMetaInfo (getMetaInfo mv) $ do
      args <- getContextArgs
      noConstraints $ assignV mI args v

