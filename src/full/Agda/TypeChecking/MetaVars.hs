{-# LANGUAGE CPP, RelaxedPolyRec, GeneralizedNewtypeDeriving #-}

module Agda.TypeChecking.MetaVars where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import Data.Generics
import Data.List as List hiding (sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
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
isBlockedTerm :: MonadTCM tcm => MetaId -> tcm Bool
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

isEtaExpandable :: MonadTCM tcm => MetaId -> tcm Bool
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
assignTerm' :: MonadTCM tcm => Bool -> MetaId -> Term -> tcm ()
assignTerm' assigningSort x t = do
    reportSLn "tc.meta.assign" 70 $ show x ++ " := " ++ show t
    whenM (isFrozen x) __IMPOSSIBLE__  -- verify (new) invariant
    let i = metaInstance (killRange t)
    modifyMetaStore $ ins x i
    etaExpandListeners x
    wakeupConstraints
    reportSLn "tc.meta.assign" 20 $ "completed assignment of " ++ show x
  where
    metaInstance = InstV -- if assigningSort then InstS else InstV
    ins x i store = Map.adjust (inst i) x store
    inst i mv = mv { mvInstantiation = i }

assignTerm :: MonadTCM tcm => MetaId -> Term -> tcm ()
assignTerm = assignTerm' False

{- UNUSED
assignSort :: MonadTCM tcm => MetaId -> Sort -> tcm ()
assignSort x s = assignTerm' True x (Sort s)
-}

-- * Creating meta variables.

newSortMeta :: MonadTCM tcm => tcm Sort
newSortMeta =
  ifM typeInType (return $ mkType 0) $
  ifM hasUniversePolymorphism (newSortMetaCtx =<< getContextArgs)
  -- else (no universe polymorphism)
  $ do i <- createMetaInfo
       x <- newMeta i normalMetaPriority (idP 0) (IsSort () topSort)
       return $ Type $ Max [Plus 0 $ MetaLevel x []]

newSortMetaCtx :: MonadTCM tcm => Args -> tcm Sort
newSortMetaCtx vs =
  ifM typeInType (return $ mkType 0) $ do
    i   <- createMetaInfo
    tel <- getContextTelescope
    let t = telePi_ tel topSort
    x   <- newMeta i normalMetaPriority (idP 0) (IsSort () t)
    reportSDoc "tc.meta.new" 50 $
      text "new sort meta" <+> prettyTCM x <+> text ":" <+> prettyTCM t
    return $ Type $ Max [Plus 0 $ MetaLevel x vs]

newTypeMeta :: MonadTCM tcm => Sort -> tcm Type
newTypeMeta s = El s <$> newValueMeta (sort s)

newTypeMeta_ ::  MonadTCM tcm => tcm Type
newTypeMeta_  = newTypeMeta =<< (workOnTypes $ newSortMeta)
-- TODO: (this could be made work with new uni-poly)
-- Andreas, 2011-04-27: If a type meta gets solved, than we do not have to check
-- that it has a sort.  The sort comes from the solution.
-- newTypeMeta_  = newTypeMeta Inf

-- | Create a new "implicit from scope" metavariable
newIFSMeta ::  MonadTCM tcm => Type -> tcm (Term, ConstraintClosure)
newIFSMeta t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newIFSMetaCtx (telePi_ tel t) vs

-- | Create a new value meta with specific dependencies.
newIFSMetaCtx :: MonadTCM tcm => Type -> Args -> tcm (Term, ConstraintClosure)
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
  c <- buildConstraint' $ FindInScope x
  return (MetaV x vs, c)

-- | Create a new metavariable, possibly η-expanding in the process.
newValueMeta ::  MonadTCM tcm => Type -> tcm Term
newValueMeta t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx (telePi_ tel t) vs

newValueMetaCtx :: MonadTCM tcm => Type -> Args -> tcm Term
newValueMetaCtx t ctx = do
  m@(MetaV i _) <- newValueMetaCtx' t ctx
  instantiateFull m

-- | Create a new value meta without η-expanding.
newValueMeta' :: MonadTCM tcm => Type -> tcm Term
newValueMeta' t = do
  vs  <- getContextArgs
  tel <- getContextTelescope
  newValueMetaCtx' (telePi_ tel t) vs

-- | Create a new value meta with specific dependencies.
newValueMetaCtx' :: MonadTCM tcm => Type -> Args -> tcm Term
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

newTelMeta :: MonadTCM tcm => Telescope -> tcm Args
newTelMeta tel = newArgsMeta (abstract tel $ El Prop $ Sort Prop)

newArgsMeta :: MonadTCM tcm => Type -> tcm Args
newArgsMeta t = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newArgsMetaCtx t tel args

newArgsMetaCtx :: MonadTCM tcm => Type -> Telescope -> Args -> tcm Args
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
newRecordMeta :: MonadTCM tcm => QName -> Args -> tcm Term
newRecordMeta r pars = do
  args <- getContextArgs
  tel  <- getContextTelescope
  newRecordMetaCtx r pars tel args

newRecordMetaCtx :: MonadTCM tcm => QName -> Args -> Telescope -> Args -> tcm Term
newRecordMetaCtx r pars tel ctx = do
  ftel	 <- flip apply pars <$> getRecordFieldTypes r
  fields <- newArgsMetaCtx (telePi_ ftel $ sort Prop) tel ctx
  con    <- getRecordConstructor r
  return $ Con con fields

newQuestionMark :: MonadTCM tcm => Type -> tcm Term
newQuestionMark t = do
  m@(MetaV x _) <- newValueMeta' t
  ii		<- fresh
  addInteractionPoint ii x
  return m

-- | Construct a blocked constant if there are constraints.
blockTerm :: MonadTCM tcm => Type -> Term -> tcm Constraints -> tcm Term
blockTerm t v m = do
    cs <- solveConstraints =<< m
    if List.null cs
	then return v
	else do
	    i	  <- createMetaInfo
	    vs	  <- getContextArgs
	    tel   <- getContextTelescope
	    x	  <- newMeta' (BlockedConst $ abstract tel v)
                              i lowMetaPriority (idP $ size tel)
                              (HasType () $ telePi_ tel t)
			    -- we don't instantiate blocked terms
	    c <- escapeContext (size tel) $ guardConstraint (return cs) (UnBlock x)
            verboseS "tc.meta.blocked" 20 $ do
                dx  <- prettyTCM (MetaV x [])
                dv  <- escapeContext (size tel) $ prettyTCM $ abstract tel v
                dcs <- mapM prettyTCM cs
                liftIO $ LocIO.putStrLn $ "blocked " ++ show dx ++ " := " ++ show dv
                liftIO $ LocIO.putStrLn $ "     by " ++ show dcs
	    addConstraints c
	    return $ MetaV x vs

-- | @unblockedTester t@ returns @False@ if @t@ is a meta or a blocked term.
--
--   Auxiliary function to create a postponed type checking problem.
unblockedTester :: MonadTCM tcm => Type -> tcm Bool
unblockedTester t = do
  t <- reduceB $ unEl t
  case t of
    Blocked{}          -> return False
    NotBlocked MetaV{} -> return False
    _                  -> return True

-- | Create a postponed type checking problem @e : t@ that waits for type @t@
--   to unblock (become instantiated or its constraints resolved).
postponeTypeCheckingProblem_ :: MonadTCM tcm => A.Expr -> Type -> tcm Term
postponeTypeCheckingProblem_ e t = do
  postponeTypeCheckingProblem e t (unblockedTester t)

-- | Create a postponed type checking problem @e : t@ that waits for conditon
--   @unblock@.  A new meta is created in the current context that has as
--   instantiation the postponed type checking problem.  An 'UnBlock' constraint
--   is added for this meta, which links to this meta.
postponeTypeCheckingProblem :: MonadTCM tcm => A.Expr -> Type -> TCM Bool -> tcm Term
postponeTypeCheckingProblem e t unblock = do
  i   <- createMetaInfo
  tel <- getContextTelescope
  cl  <- buildClosure (e, t, unblock)
  m   <- newMeta' (PostponedTypeCheckingProblem cl)
                  i normalMetaPriority (idP (size tel))
         $ HasType () $ telePi_ tel t
  addConstraints =<< buildConstraint (UnBlock m)
  MetaV m <$> getContextArgs

-- | Eta expand metavariables listening on the current meta.
etaExpandListeners :: MonadTCM tcm => MetaId -> tcm ()
etaExpandListeners m = do
  ms <- getMetaListeners m
  clearMetaListeners m	-- we don't really have to do this
  -- Andreas 2010-10-15: do not expand record mvars, lazyness needed for irrelevance
  mapM_ etaExpandMetaSafe ms
--  mapM_ (etaExpandMeta allMetaKinds) ms

-- | Do safe eta-expansions for meta (@SingletonRecords,Levels@).
etaExpandMetaSafe :: MonadTCM tcm => MetaId -> tcm ()
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
etaExpandMeta :: MonadTCM tcm => [MetaKind] -> MetaId -> tcm ()
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
    Blocked x _               -> listenToMeta m x
    NotBlocked (MetaV x _)    -> listenToMeta m x
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
            Left x      -> listenToMeta m x
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

etaExpandBlocked
  :: (MonadTCM tcm, Reduce t) => Blocked t -> tcm (Blocked t)
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

assignV :: MonadTCM tcm => MetaId -> Args -> Term -> tcm Constraints
assignV x args v = do
	reportSDoc "tc.meta.assign" 10 $ do
	  text "term" <+> prettyTCM (MetaV x args) <+> text ":=" <+> prettyTCM v
        assign False x args v

assignS :: MonadTCM tcm => MetaId -> Args -> Sort -> tcm Constraints
assignS x args s =
  ifM (not <$> hasUniversePolymorphism) (noPolyAssign x s) $ do
	reportSDoc "tc.meta.assign" 10 $ do
	  text "sort" <+> prettyTCM (Type $ Max [Plus 0 $ MetaLevel x args]) <+> text ":=" <+> prettyTCM s
        assign True x args (Sort s)
    where
        noPolyAssign x s = do
            -- We don't instantiate frozen mvars
            whenM (isFrozen x) patternViolation
            assignTerm' True x =<< occursCheck x [] (Sort s)
--            Sort s <- occursCheck x [] (Sort s)
--            x =: s
            return []

-- | @assign sort? x vs v@
assign :: MonadTCM tcm => Bool -> MetaId -> Args -> Term -> tcm Constraints
assign assigningSort x args v = do
        mvar <- lookupMeta x  -- information associated with meta x

        -- Andreas, 2011-05-20 TODO!
        -- full normalization  (which also happens during occurs check)
        -- is too expensive! (see Issue 415)
        -- need to do something cheaper, especially if
        -- we are dealing with a Miller pattern that can be solved
        -- immediately!
        reportSLn "tc.meta.assign" 50 $ "MetaVars.assign: normalizing v = " ++ (show v)
        v <- normalise v
        reportSLn "tc.meta.assign" 50 $ "MetaVars.assign: finished normalizing v = " ++ (show v)

        case (v, mvJudgement mvar) of
            (Sort Inf, HasType{}) -> typeError $ GenericError "Setω is not a valid type."
            _                     -> return ()

        -- We don't instantiate frozen mvars
        when (mvFrozen mvar == Frozen) $ do
          reportSLn "tc.meta.assign" 25 $ "aborting: meta is frozen!"
          patternViolation

	-- We don't instantiate blocked terms
	whenM (isBlockedTerm x) patternViolation	-- TODO: not so nice

        -- Andreas, 2010-10-15 I want to see whether rhs is blocked
        reportSLn "tc.meta.assign" 50 $ "MetaVars.assign: I want to see whether rhs is blocked"
        reportSDoc "tc.meta.assign" 25 $ do
          v0 <- reduceB v
          case v0 of
            Blocked m0 _ -> text "r.h.s. blocked on:" <+> prettyTCM m0
            NotBlocked{} -> text "r.h.s. not blocked"

        -- Andreas, 2011-04-21 do the occurs check first
        -- e.g. _1 x (suc x) = suc (_2 x y)
        -- even though the lhs is not a pattern, we can prune the y from _2
        let fvsL = Set.toList $ allVars $ freeVars args
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

        let fvs' = freeVars v
        -- Andreas, 2011-04-26: The following piece of code is from assignS
        -- I do not know why it is there.
        -- BEGIN  "-- TODO Hack"
        when (any (< 0) $ Set.toList (flexibleVars fvs')) $ do
            reportSLn "tc.meta.assign" 10 "negative variables!"
            patternViolation
        -- END

        -- Check linearity of @ids@
        -- Andreas, 2010-09-24: Herein, ignore the variables which are not
        -- free in v
        let fvs = allVars $ fvs'
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
--	escapeContext n $ x =: killRange (abstract tel' v')
	escapeContext n $ assignTerm' assigningSort x $ killRange (abstract tel' v')
	return []
    where
        rename :: [Nat] -> Nat -> Arg Term -> Arg Term
	rename ids i arg = case findIndex (==i) ids of
	    Just j  -> fmap (const $ Var (fromIntegral j) []) arg
--	    Nothing -> fmap (const DontCare) arg	-- we will end up here, but never look at the result
	    Nothing -> fmap (const __IMPOSSIBLE__) arg	-- we will end up here, but never look at the result

type FVs = Set Nat

-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--   Parameters are represented as @Var@s so @checkArgs@ really
--     checks that all args are @Var@s and returns the
--     list of corresponding indices for each arg.
--   Linearity has to be checked separately.
--
--   @reverse@ is necessary because we are directly abstracting over this list @ids@.
checkAllVars :: MonadTCM tcm => Args -> tcm [Nat]
checkAllVars args = do
  args <- instantiateFull args
  maybe patternViolation (return . map unArg) $ allVarOrIrrelevant args

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


updateMeta :: (MonadTCM tcm, Data a, Occurs a, Abstract a) => MetaId -> a -> tcm ()
updateMeta mI t =
    do	mv <- lookupMeta mI
	withMetaInfo (getMetaInfo mv) $
	    do	args <- getContextArgs
		cs <- upd mI args (mvJudgement mv) t
		unless (List.null cs) $ fail $ "failed to update meta " ++ show mI
    where
	upd mI args j t = (__IMPOSSIBLE__ `mkQ` updV j `extQ` updS) t
	    where
		updV (HasType _ t) v =
		  assignV mI args v
		updV _ _	     = __IMPOSSIBLE__

		updS s = assignS mI args s
