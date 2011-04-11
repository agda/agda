{-# LANGUAGE CPP, RelaxedPolyRec, GeneralizedNewtypeDeriving #-}

module Agda.TypeChecking.MetaVars where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import Data.Generics
import Data.Map (Map)
import Data.Set (Set)
import Data.List as List hiding (sort)
import qualified Data.Map as Map
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
import Agda.TypeChecking.EtaContract

import Agda.TypeChecking.MetaVars.Occurs

import {-# SOURCE #-} Agda.TypeChecking.Conversion

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
    reportSLn "tc.meta.blocked" 12 $
      if r then "  yes, because " ++ show i else "  no"
    return r

isEtaExpandable :: MonadTCM tcm => MetaId -> tcm Bool
isEtaExpandable x = do
    i <- mvInstantiation <$> lookupMeta x
    return $ case i of
      Open{}                         -> True
      InstV{}                        -> False
      InstS{}                        -> False
      BlockedConst{}                 -> False
      PostponedTypeCheckingProblem{} -> False

-- * Performing the assignment

class HasMeta t where
    metaInstance :: MonadTCM tcm => t -> tcm MetaInstantiation
    metaVariable :: MetaId -> Args -> t

-- | Performing the meta variable assignment.
--
--   The instantiation should not be an 'InstV' or 'InstS' and the 'MetaId'
--   should point to something 'Open' or a 'BlockedConst'.
--   Further, the meta variable may not be 'Frozen'.
(=:) :: (MonadTCM tcm, HasMeta t, KillRange t, Show t) =>
        MetaId -> t -> tcm ()
x =: t = do
    reportSLn "tc.meta.assign" 70 $ show x ++ " := " ++ show t
    whenM (isFrozen x) __IMPOSSIBLE__  -- verify (new) invariant
    i <- metaInstance (killRange t)
    modifyMetaStore $ ins x i
    etaExpandListeners x
    wakeupConstraints
    reportSLn "tc.meta.assign" 20 $ "completed assignment of " ++ show x
  where
    ins x i store = Map.adjust (inst i) x store
    inst i mv = mv { mvInstantiation = i }

-- ** Instance for terms.

instance HasMeta Term where
    metaInstance = return . InstV
    metaVariable = MetaV

assignTerm :: MonadTCM tcm => MetaId -> Term -> tcm ()
assignTerm = (=:)

-- ** Instance for sorts.

instance HasMeta Sort where
    metaInstance = return . InstS . Sort
    metaVariable = MetaS

-- | A wrapper for sorts represented as terms.
newtype SortTerm = SortTerm { unSortTerm :: Term }
    deriving (Eq, Ord, Show, KillRange)

instance HasMeta SortTerm where
    metaInstance = return . InstS . unSortTerm
    metaVariable x vs = SortTerm (MetaV x vs)

(=:=) :: (MonadTCM tcm) => MetaId -> Term -> tcm ()
x =:= t = x =: (SortTerm t)



newSortMeta :: MonadTCM tcm => tcm Sort
newSortMeta =
  ifM typeInType (return $ mkType 0) $
  ifM hasUniversePolymorphism (newSortMetaCtx =<< getContextArgs)
  $ do i <- createMetaInfo
       x <- newMeta i normalMetaPriority (idP 0) (IsSort())
       return $ MetaS x []

newSortMetaCtx :: MonadTCM tcm => Args -> tcm Sort
newSortMetaCtx vs =
  ifM typeInType (return $ mkType 0) $ do
    i <- createMetaInfo
    x <- newMeta i normalMetaPriority (idP 0) (IsSort ())
    return $ MetaS x vs

newTypeMeta :: MonadTCM tcm => Sort -> tcm Type
newTypeMeta s = El s <$> newValueMeta (sort s)

newTypeMeta_ ::  MonadTCM tcm => tcm Type
newTypeMeta_  = newTypeMeta =<< newSortMeta

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

-- | Auxiliary function to create a postponed type checking problem.
unblockedTester :: MonadTCM tcm => Type -> tcm Bool
unblockedTester t = do
  t <- reduceB $ unEl t
  case t of
    Blocked{}          -> return False
    NotBlocked MetaV{} -> return False
    _                  -> return True

postponeTypeCheckingProblem_ :: MonadTCM tcm => A.Expr -> Type -> tcm Term
postponeTypeCheckingProblem_ e t = do
  postponeTypeCheckingProblem e t (unblockedTester t)

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
                noConstraints $ assignV b m args u  -- should never produce any constraints
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
          noConstraints $ assignV b m args (Lit $ LitLevel noRange 0)
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

abortAssign :: MonadTCM tcm => tcm a
abortAssign =
    do	s <- get
	liftTCM $ throwError $ TCErr Nothing $ AbortAssign s

handleAbort :: MonadTCM tcm => TCM a -> TCM a -> tcm a
handleAbort h m = liftTCM $
    m `catchError_` \e ->
	case errError e of
	    AbortAssign s -> do put s; h
            PatternErr{}  -> do
              -- Andreas, 2010-09-17 uncommenting the reportSLn statements
              -- breaks something.  Why?
              -- reportSLn "tc.meta.assign" 50 "handleAbort: Pattern violation!"
              throwError e
	    _		  -> do
              -- reportSLn "tc.meta.assign" 50 "handleAbort: Some exception"
              throwError e

-- | Assign to an open metavar which may not be frozen.
--   First check that metavar args are in pattern fragment.
--     Then do extended occurs check on given thing.
--
assignV :: MonadTCM tcm => Type -> MetaId -> Args -> Term -> tcm Constraints
assignV t x args v =
    handleAbort handler $ do
	reportSDoc "tc.meta.assign" 10 $ do
	  text "term" <+> prettyTCM (MetaV x args) <+> text ":=" <+> prettyTCM v

        v <- normalise v
        case v of
          Sort Inf  -> typeError $ GenericError "Setω is not a valid type."
          _         -> return ()

        -- We don't instantiate frozen mvars
        whenM (isFrozen x) patternViolation

	-- We don't instantiate blocked terms
	whenM (isBlockedTerm x) patternViolation	-- TODO: not so nice

	-- Check that the arguments are distinct variables
        -- Andreas, 2010-09-24: Herein, ignore the variables which are not
        -- free in v
        let fvs = allVars $ freeVars v
        reportSDoc "tc.meta.assign" 20 $
            let pr (Var n []) = text (show n)
                pr (Def c []) = prettyTCM c
                pr _          = text ".."
            in vcat
                 [ text "mvar args:" <+> sep (map (pr . unArg) args)
                 , text "fvars rhs:" <+> sep (map (text . show) $ Set.toList fvs)
                 ]
	ids <- checkArgs x args fvs

	reportSDoc "tc.meta.assign" 15 $
	    text "preparing to instantiate: " <+> prettyTCM v

        -- Andreas, 2010-10-15 I want to see whether rhd is blocked
        reportSDoc "tc.meta.assign" 25 $ do
          v0 <- reduceB v
          case v0 of
            Blocked m0 _ -> text "blocked on:" <+> prettyTCM m0
            NotBlocked{} -> text "not blocked"

	-- Check that the x doesn't occur in the right hand side
	v <- liftTCM $ occursCheck x (map unArg ids) v

	verboseS "tc.conv.assign" 30 $ do
	  let n = size v
	  when (n > 200) $ do
	    r <- getMetaRange x
	    d <- sep [ text "size" <+> text (show n)
		     , nest 2 $ text "type" <+> prettyTCM t
		     , nest 2 $ text "term" <+> prettyTCM v
		     ]
	    liftIO $ LocIO.print d

	reportSLn "tc.meta.assign" 15 "passed occursCheck"

	-- Rename the variables in v to make it suitable for abstraction over ids.
	v' <- do
	    -- Basically, if
	    --   Γ   = a b c d e
	    --   ids = d b e
	    -- then
	    --   v' = (λ a b c d e. v) _ 1 _ 2 0
	    tel  <- getContextTelescope
	    args <- map defaultArg <$> getContextTerms
	    let iargs = reverse $ zipWith (rename $ reverse $ map unArg ids) [0..] $ reverse args
		v'    = raise (size ids) (abstract tel v) `apply` iargs
	    return v'

	let extTel (Arg h r i) m = do
	      tel <- m
	      t	  <- typeOfBV i
	      x	  <- nameOfBV i
	      return $ ExtendTel (Arg h r t) (Abs (show x) tel)
	tel' <- foldr extTel (return EmptyTel) ids

	reportSDoc "tc.meta.assign" 15 $
	  text "final instantiation:" <+> prettyTCM (abstract tel' v')

	-- Perform the assignment (and wake constraints). Metas
	-- are top-level so we do the assignment at top-level.
	n <- size <$> getContextTelescope
	escapeContext n $ x =: killRange (abstract tel' v')
	return []
    where
	rename ids i arg = case findIndex (==i) ids of
	    Just j  -> fmap (const $ Var (fromIntegral j) []) arg
	    Nothing -> fmap (const __IMPOSSIBLE__) arg	-- we will end up here, but never look at the result

	handler :: MonadTCM tcm => tcm Constraints
	handler = do
	    reportSLn "tc.meta.assign" 10 $ "Oops. Undo " ++ show x ++ " := ..."
	    equalTerm t (MetaV x args) v

-- TODO: Unify with assignV
assignS :: MonadTCM tcm => MetaId -> Args -> Sort -> tcm Constraints
assignS x args s =
  ifM (not <$> hasUniversePolymorphism) (noPolyAssign x s) $
    handleAbort handler $ do
	reportSDoc "tc.meta.assign" 10 $ do
	  text "sort" <+> prettyTCM (MetaS x args) <+> text ":=" <+> prettyTCM s

        -- We don't instantiate frozen mvars
        whenM (isFrozen x) patternViolation

	-- We don't instantiate blocked terms
	whenM (isBlockedTerm x) patternViolation	-- TODO: not so nice

	-- Check that the arguments are distinct variables
        reportSDoc "tc.meta.assign" 20 $
            let pr (Var n []) = text (show n)
                pr (Def c []) = prettyTCM c
                pr _          = text ".."
            in
            text "args:" <+> sep (map (pr . unArg) args)

        -- TODO Hack
        let fvs = freeVars s
        when (any (< 0) $ Set.toList (flexibleVars fvs)) $ do
            reportSLn "tc.meta.assign" 10 "negative variables!"
            patternViolation

	ids <- checkArgs x args (allVars fvs)

	reportSDoc "tc.meta.assign" 15 $
	    text "preparing to instantiate: " <+> prettyTCM s

	-- Check that the x doesn't occur in the right hand side
	v <- liftTCM $ occursCheck x (map unArg ids) (Sort s)

	verboseS "tc.conv.assign" 30 $ do
	  let n = size v
	  when (n > 200) $ do
	    r <- getMetaRange x
	    d <- sep [ text "size" <+> text (show n)
		     , nest 2 $ text "sort" <+> prettyTCM v
		     ]
	    liftIO $ LocIO.print d

	reportSLn "tc.meta.assign" 15 "passed occursCheck"

	-- Rename the variables in v to make it suitable for abstraction over ids.
	v' <- do
	    -- Basically, if
	    --   Γ   = a b c d e
	    --   ids = d b e
	    -- then
	    --   v' = (λ a b c d e. v) _ 1 _ 2 0
	    tel  <- getContextTelescope
	    args <- map defaultArg <$> getContextTerms
	    let iargs = reverse $ zipWith (rename $ reverse $ map unArg ids) [0..] $ reverse args
		v'    = raise (size ids) (abstract tel v) `apply` iargs
	    return v'

	let extTel (Arg h r i) m = do
	      tel <- m
	      t	  <- typeOfBV i
	      x	  <- nameOfBV i
	      return $ ExtendTel (Arg h r t) (Abs (show x) tel)
	tel' <- foldr extTel (return EmptyTel) ids

	reportSDoc "tc.meta.assign" 15 $
	  text "final instantiation:" <+> prettyTCM (abstract tel' v')

	-- Perform the assignment (and wake constraints). Metas
	-- are top-level so we do the assignment at top-level.
	n <- size <$> getContextTelescope
	escapeContext n $ x =:= killRange (abstract tel' v')
	return []
    where
	rename ids i arg = case findIndex (==i) ids of
	    Just j  -> fmap (const $ Var (fromIntegral j) []) arg
	    Nothing -> fmap (const __IMPOSSIBLE__) arg
              -- we will end up here, but never look at the result

	handler :: MonadTCM tcm => tcm Constraints
	handler = do
	    reportSLn "tc.meta.assign" 10 $ "Oops. Undo " ++ show x ++ " := ..."
	    equalSort (MetaS x args) s

        noPolyAssign x s =
          handleAbort (equalSort (MetaS x []) s) $ do

            -- We don't instantiate frozen mvars
            whenM (isFrozen x) patternViolation

            Sort s <- occursCheck x [] (Sort s)
            x =: s
            return []

type FVs = Set Nat

-- | Check that arguments to a metavar are in pattern fragment.
--   Assumes all arguments already in whnf.
--   Parameters are represented as @Var@s so @checkArgs@ really
--     checks that all args are unique @Var@s and returns the
--     list of corresponding indices for each arg-- done
--     to not define equality on @Term@.
--
--   @reverse@ is necessary because we are directly abstracting over this list @ids@.
--
checkArgs :: MonadTCM tcm => MetaId -> Args -> FVs -> tcm [Arg Nat]
checkArgs x args fvs = do
  args <- instantiateFull args
  case validParameters args fvs of
    Just ids -> return $ reverse ids
    Nothing  -> patternViolation

-- | Check that the parameters to a meta variable are distinct variables.
-- Andreas, 2010-09-24: Allow non-linear variables that do not appear in @FVs@.
validParameters :: Monad m => Args -> FVs -> m [Arg Nat]
validParameters args fvs
    | all isVar args && distinct (filter (flip Set.member fvs) $ map unArg vars)
                = return $ reverse vars
    | otherwise	= fail "invalid parameters"
    where
	vars = [ Arg h r i | Arg h r (Var i []) <- args ]


isVar :: Arg Term -> Bool
isVar (Arg _ _ (Var _ [])) = True
isVar _			 = False


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
		  assignV (t `piApply` args) mI args v
		updV _ _	     = __IMPOSSIBLE__

		updS s = assignS mI args s
