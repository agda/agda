{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE UndecidableInstances #-}

{- | The occurs check for unification.  Does pruning on the fly.

  When hitting a meta variable:

  - Compute flex/rigid for its arguments.
  - Compare to allowed variables.
  - Mark arguments with rigid occurrences of disallowed variables for deletion.
  - Attempt to delete marked arguments.
  - We don't need to check for success, we can just continue occurs checking.
-}

module Agda.TypeChecking.MetaVars.Occurs where

import Control.Monad
import Control.Monad.Reader

import Data.Foldable (foldMap)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Data.Traversable (traverse)

import qualified Agda.Benchmarking as Bench

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free hiding (Occurrence(..))
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import {-# SOURCE #-} Agda.TypeChecking.MetaVars

import Agda.Utils.Either

import Agda.Utils.Except
  ( ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )

import Agda.Utils.Lens
import Agda.Utils.List (downFrom)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size

import Agda.Utils.Impossible

{- To address issue 585 (meta var occurrences in mutual defs)

data B : Set where
  inn : A -> B

out : B -> A
out (inn a) = a

postulate
  P : (y : A) (z : Unit -> B) → Set
  p : (x : Unit -> B) → P (out (x unit)) x

mutual
  d : Unit -> B
  d unit = inn _           -- Y

  g : P (out (d unit)) d
  g = p _             -- X

-- Agda solves  d unit = inn (out (d unit))
--
-- out (X unit) = out (d unit) = out (inn Y) = Y
-- X = d

When doing the occurs check on d, we need to look at the definition of
d to discover that it mentions X.

To this end, we extend the state by names of definitions that have to
be checked when they occur.  At the beginning, this is initialized
with the names in the current mutual block.  Each time we encounter a
name in the list during occurs check, we delete it (if check is
successful).  This way, we do not duplicate work.

-}

modifyOccursCheckDefs :: (Set QName -> Set QName) -> TCM ()
modifyOccursCheckDefs f = stOccursCheckDefs `modifyTCLens` f

-- | Set the names of definitions to be looked at
--   to the defs in the current mutual block.
initOccursCheck :: MetaVariable -> TCM ()
initOccursCheck mv = modifyOccursCheckDefs . const =<<
  if (miMetaOccursCheck (mvInfo mv) == DontRunMetaOccursCheck)
   then do
     reportSLn "tc.meta.occurs" 20 $
       "initOccursCheck: we do not look into definitions"
     return Set.empty
   else do
     reportSLn "tc.meta.occurs" 20 $
       "initOccursCheck: we look into the following definitions:"
     mb <- asksTC envMutualBlock
     case mb of
       Nothing -> do
         reportSLn "tc.meta.occurs" 20 $ "(none)"
         return Set.empty
       Just b  -> do
         ds <- mutualNames <$> lookupMutualBlock b
         reportSDoc "tc.meta.occurs" 20 $ sep $ map prettyTCM $ Set.toList ds
         return ds


-- | Is a def in the list of stuff to be checked?
defNeedsChecking :: QName -> TCM Bool
defNeedsChecking d = Set.member d <$> useTC stOccursCheckDefs

-- | Remove a def from the list of defs to be looked at.
tallyDef :: QName -> TCM ()
tallyDef d = modifyOccursCheckDefs $ \ s -> Set.delete d s

data OccursCtx
  = Flex          -- ^ We are in arguments of a meta.
  | Rigid         -- ^ We are not in arguments of a meta but a bound var.
  | StronglyRigid -- ^ We are at the start or in the arguments of a constructor.
  | Irrel         -- ^ We are in an irrelevant argument.
  deriving (Eq, Show)

data UnfoldStrategy = YesUnfold | NoUnfold
  deriving (Eq, Show)

defArgs :: UnfoldStrategy -> OccursCtx -> OccursCtx
defArgs NoUnfold  _   = Flex
defArgs YesUnfold ctx = weakly ctx

unfold :: UnfoldStrategy -> Term -> TCM (Blocked Term)
unfold NoUnfold  v = notBlocked <$> instantiate v
unfold YesUnfold v = reduceB v

-- | Leave the strongly rigid position.
weakly :: OccursCtx -> OccursCtx
weakly StronglyRigid = Rigid
weakly ctx = ctx

strongly :: OccursCtx -> OccursCtx
strongly Rigid = StronglyRigid
strongly ctx = ctx

patternViolation' :: Int -> String -> TCM a
patternViolation' n err = do
  reportSLn "tc.meta.occurs" n err
  patternViolation

abort :: OccursCtx -> TypeError -> TCM a
abort StronglyRigid err = typeError err -- here, throw an uncatchable error (unsolvable constraint)
abort Flex          err = patternViolation' 70 (show err) -- throws a PatternErr, which leads to delayed constraint
abort Rigid         err = patternViolation' 70 (show err)
abort Irrel         err = patternViolation' 70 (show err)

-- | Distinguish relevant, irrelevant and nonstrict variables in occurs check.
type Vars = ([Nat],[Nat],[Nat])
-- TODO: refactor this into an actual datatype

goIrrelevant :: Vars -> Vars
goIrrelevant (relVs, nonstrictVs, irrVs) = (irrVs ++ nonstrictVs ++ relVs, [], [])

goNonStrict :: Vars -> Vars
goNonStrict (relVs, nonstrictVs, irrVs) = (nonstrictVs ++ relVs, [], irrVs)

allowedVar :: Nat -> Vars -> Bool
allowedVar i (relVs, nonstrictVs, irrVs) = i `elem` relVs

takeRelevant :: Vars -> [Nat]
takeRelevant (relVs, nonstrictVs, irrVs) = relVs

takeAll :: Vars -> [Nat]
takeAll (rel, nst, irr) = rel ++ nst ++ irr

liftUnderAbs :: Vars -> Vars
liftUnderAbs (relVs, nonstrictVs, irrVs) = (0 : map (1+) relVs, map (+1) nonstrictVs, map (1+) irrVs)

-- | Extended occurs check.
class Occurs t where
  occurs :: UnfoldStrategy -> OccursCtx -> MetaId -> Vars -> t -> TCM t
  metaOccurs :: MetaId -> t -> TCM ()  -- raise exception if meta occurs in t

-- | When assigning @m xs := v@, check that @m@ does not occur in @v@
--   and that the free variables of @v@ are contained in @xs@.
occursCheck
  :: (Occurs a, InstantiateFull a, PrettyTCM a)
  => MetaId -> Vars -> a -> TCM a
occursCheck m xs v = Bench.billTo [ Bench.Typing, Bench.OccursCheck ] $ do
  mv <- lookupMeta m
  let ctx = if isIrrelevant (getMetaRelevance mv) then Irrel else StronglyRigid
  initOccursCheck mv
      -- TODO: Can we do this in a better way?
  let redo m = m
  -- First try without normalising the term
  redo (occurs NoUnfold  ctx m xs v) `catchError` \_ -> do
    initOccursCheck mv
    redo (occurs YesUnfold ctx m xs v) `catchError` \err -> case err of
                            -- Produce nicer error messages
      TypeError _ cl -> case clValue cl of
        MetaOccursInItself{} ->
          typeError . GenericError . show =<<
            fsep [ text ("Refuse to construct infinite term by instantiating " ++ prettyShow m ++ " to")
                 , prettyTCM =<< instantiateFull v
                 ]
        MetaCannotDependOn _ _ i ->
          ifM (isSortMeta m `and2M` (not <$> hasUniversePolymorphism))
          ( typeError . GenericError . show =<<
            fsep [ text ("Cannot instantiate the metavariable " ++ prettyShow m ++ " to")
                 , prettyTCM v
                 , "since universe polymorphism is disabled"
                 ]
          ) {- else -}
          ( typeError . GenericError . show =<<
              fsep [ text ("Cannot instantiate the metavariable " ++ prettyShow m ++ " to solution")
                   , prettyTCM v
                   , "since it contains the variable"
                   , enterClosure cl $ \_ -> prettyTCM (Var i [])
                   , text $ "which is not in scope of the metavariable or irrelevant in the metavariable but relevant in the solution"
                   ]
            )
        MetaIrrelevantSolution _ _ ->
          typeError . GenericError . show =<<
            fsep [ text ("Cannot instantiate the metavariable " ++ prettyShow m ++ " to solution")
                 , prettyTCM v
                 , "since (part of) the solution was created in an irrelevant context."
                 ]
        _ -> throwError err
      _ -> throwError err

instance Occurs Term where
  occurs red ctx m xs v = do
    v <- unfold red v
    -- occurs' ctx $ ignoreBlocking v  -- fails test/succeed/DontPruneBlocked
    case v of
      -- Don't fail on blocked terms or metas
      NotBlocked _ v      -> occurs' ctx v
      -- Blocked _ v@MetaV{} -> occurs' ctx v  -- does not help with issue 856
      Blocked _ v         -> occurs' Flex v
    where
      occurs' ctx v = do
        reportSDoc "tc.meta.occurs" 45 $
          text ("occursCheck " ++ prettyShow m ++ " (" ++ show ctx ++ ") of ") <+> prettyTCM v
        reportSDoc "tc.meta.occurs" 70 $
          nest 2 $ text $ show v
        case v of
          Var i es   -> do
            if (i `allowedVar` xs) then Var i <$> occ (weakly ctx) es else do
              -- if the offending variable is of singleton type,
              -- eta-expand it away
              reportSDoc "tc.meta.occurs" 35 $ "offending variable: " <+> prettyTCM (var i)
              t <-  typeOfBV i
              reportSDoc "tc.meta.occurs" 35 $ nest 2 $ "of type " <+> prettyTCM t
              isST <- isSingletonType t
              reportSDoc "tc.meta.occurs" 35 $ nest 2 $ "(after singleton test)"
              case isST of
                -- cannot decide, blocked by meta-var
                Left mid -> patternViolation' 70 $ "Disallowed var " ++ show i ++ " not obviously singleton"
                -- not a singleton type
                Right Nothing -> -- abort Rigid turns this error into PatternErr
                  abort (strongly ctx) $ MetaCannotDependOn m (takeRelevant xs) i
                -- is a singleton type with unique inhabitant sv
                Right (Just sv) -> return $ sv `applyE` es
          Lam h f     -> Lam h <$> occ ctx f
          Level l     -> Level <$> occ ctx l
          Lit l       -> return v
          Dummy{}     -> return v
          DontCare v  -> if ctx == Irrel then
                           dontCare <$> occurs red ctx m xs v
                         else
                           abort (strongly ctx) $ MetaIrrelevantSolution m v
          Def d es    -> do
            drel <- relOfConst d
            unless (usableRelevance drel || ctx == Irrel) $ do
              reportSDoc "tc.meta.occurs" 35 $ text ("relevance of definition: " ++ show drel)
              abort ctx $ MetaIrrelevantSolution m $ Def d []
            Def d <$> occDef d ctx es
          Con c ci vs -> Con c ci <$> occ ctx vs  -- if strongly rigid, remain so
          Pi a b      -> uncurry Pi <$> occ ctx (a,b)
          Sort s      -> Sort <$> occurs red ctx m (goNonStrict xs) s
          MetaV m' es -> do
              -- Check for loop
              --   don't fail hard on this, since we might still be on the top-level
              --   after some killing (Issue 442)
              --
              -- Andreas, 2013-02-18  Issue 795 demonstrates that a recursive
              -- occurrence of a meta could be solved by the identity.
              --   ? (Q A) = Q (? A)
              -- So, do not throw an error.
              -- I guess the error was there from times when occurrence check
              -- was done after the "lhs=linear variables" check, but now
              -- occurrence check comes first.
              -- WAS:
              -- when (m == m') $ if ctx == Top then patternViolation else
              --   abort ctx $ MetaOccursInItself m'
              when (m == m') $ patternViolation' 50 $ "occursCheck failed: Found " ++ prettyShow m

              -- The arguments of a meta are in a flexible position
              (MetaV m' <$> occurs red Flex m xs es) `catchError` \err -> do
                reportSDoc "tc.meta.kill" 25 $ vcat
                  [ text $ "error during flexible occurs check, we are " ++ show ctx
                  , text $ show err
                  ]
                case err of
                  -- On pattern violations try to remove offending
                  -- flexible occurrences (if not already in a flexible context)
                  PatternErr{} | ctx /= Flex -> do
                    reportSLn "tc.meta.kill" 20 $
                      "oops, pattern violation for " ++ prettyShow m'
                    -- Andreas, 2014-03-02, see issue 1070:
                    -- Do not prune when meta is projected!
                    caseMaybe (allApplyElims es) (throwError err) $ \ vs -> do
                      killResult <- prune m' vs (takeAll xs)
                      if (killResult == PrunedEverything)
                        -- after successful pruning, restart occurs check
                        then occurs red ctx m xs =<< instantiate (MetaV m' es)
                        else throwError err
                  _ -> throwError err
          where
            occ ctx v = occurs red ctx m xs v
            -- a data or record type constructor propagates strong occurrences
            -- since e.g. x = List x is unsolvable
            occDef d ctx vs = do
              metaOccurs m d
              ifM (isJust <$> isDataOrRecordType d)
                {-then-} (occ ctx vs)
                {-else-} (occ (defArgs red ctx) vs)

  metaOccurs m v = do
    v <- instantiate v
    case v of
      Var i vs   -> metaOccurs m vs
      Lam h f    -> metaOccurs m f
      Level l    -> metaOccurs m l
      Lit l      -> return ()
      Dummy{}    -> return ()
      DontCare v -> metaOccurs m v
      Def d vs   -> metaOccurs m d >> metaOccurs m vs
      Con c _ vs -> metaOccurs m vs
      Pi a b     -> metaOccurs m (a,b)
      Sort s     -> metaOccurs m s
      MetaV m' vs | m == m' -> patternViolation' 50 $ "Found occurrence of " ++ prettyShow m
                  | otherwise -> metaOccurs m vs

instance Occurs QName where
  occurs red ctx m xs d = __IMPOSSIBLE__

  metaOccurs m d = whenM (defNeedsChecking d) $ do
    tallyDef d
    reportSLn "tc.meta.occurs" 30 $ "Checking for occurrences in " ++ show d
    metaOccursQName m d

metaOccursQName :: MetaId -> QName -> TCM ()
metaOccursQName m x = metaOccurs m . theDef =<< do
  ignoreAbstractMode $ getConstInfo x
  -- Andreas, 2019-05-03, issue #3742:
  -- ignoreAbstractMode necessary, as abstract
  -- constructors are also called up.

instance Occurs Defn where
  occurs red ctx m xs def = __IMPOSSIBLE__

  metaOccurs m Axiom{}                      = return ()
  metaOccurs m DataOrRecSig{}               = return ()
  metaOccurs m Function{ funClauses = cls } = metaOccurs m cls
  -- since a datatype is isomorphic to the sum of its constructor types
  -- we check the constructor types
  metaOccurs m Datatype{ dataCons = cs }    = mapM_ (metaOccursQName m) cs
  metaOccurs m Record{ recConHead = c }     = metaOccursQName m $ conName c
  metaOccurs m Constructor{}                = return ()
  metaOccurs m Primitive{}                  = return ()
  metaOccurs m AbstractDefn{}               = __IMPOSSIBLE__
  metaOccurs m GeneralizableVar{}           = __IMPOSSIBLE__

instance Occurs Clause where
  occurs red ctx m xs cl = __IMPOSSIBLE__

  metaOccurs m = metaOccurs m . clauseBody

instance Occurs Level where
  occurs red ctx m xs (Max as) = Max <$> occurs red ctx m xs as

  metaOccurs m (Max as) = metaOccurs m as

instance Occurs PlusLevel where
  occurs red ctx m xs l@ClosedLevel{} = return l
  occurs red ctx m xs (Plus n l) = Plus n <$> occurs red ctx m xs l
  metaOccurs m ClosedLevel{} = return ()
  metaOccurs m (Plus n l)    = metaOccurs m l

instance Occurs LevelAtom where
  occurs red ctx m xs l = do
    l <- case red of
           YesUnfold -> reduce l
           NoUnfold  -> instantiate l
    case l of
      MetaLevel m' args -> do
        MetaV m' args <- occurs red ctx m xs (MetaV m' args)
        return $ MetaLevel m' args
      NeutralLevel r v  -> NeutralLevel r  <$> occurs red ctx m xs v
      BlockedLevel m' v -> BlockedLevel m' <$> occurs red Flex m xs v
      UnreducedLevel v  -> UnreducedLevel  <$> occurs red ctx m xs v

  metaOccurs m l = do
    l <- instantiate l
    case l of
      MetaLevel m' args -> metaOccurs m $ MetaV m' args
      NeutralLevel _ v  -> metaOccurs m v
      BlockedLevel _ v  -> metaOccurs m v
      UnreducedLevel v  -> metaOccurs m v


instance Occurs Type where
  occurs red ctx m xs (El s v) = uncurry El <$> occurs red ctx m xs (s,v)

  metaOccurs m (El s v) = metaOccurs m (s,v)

instance Occurs Sort where
  occurs red ctx m xs s = do
    s' <- case red of
            YesUnfold -> reduce s
            NoUnfold  -> instantiate s
    case s' of
      PiSort s1 s2 -> uncurry PiSort <$> occurs red (weakly ctx) m xs (s1,s2)
      Type a     -> Type <$> occurs red ctx m xs a
      Prop a     -> Prop <$> occurs red ctx m xs a
      Inf        -> return s'
      SizeUniv   -> return s'
      UnivSort s -> UnivSort <$> occurs red (weakly ctx) m xs s
      MetaS x es -> do
        MetaV x es <- occurs red ctx m xs (MetaV x es)
        return $ MetaS x es
      DefS x es -> do
        Def x es <- occurs red ctx m xs (Def x es)
        return $ DefS x es
      DummyS{}   -> return s

  metaOccurs m s = do
    s <- instantiate s
    case s of
      PiSort s1 s2 -> metaOccurs m (s1,s2)
      Type a     -> metaOccurs m a
      Prop a     -> metaOccurs m a
      Inf        -> return ()
      SizeUniv   -> return ()
      UnivSort s -> metaOccurs m s
      MetaS x es -> metaOccurs m $ MetaV x es
      DefS d es  -> metaOccurs m $ Def d es
      DummyS{}   -> return ()

instance Occurs a => Occurs (Elim' a) where
  occurs red ctx m xs e@(Proj _ f) = do
    frel <- relOfConst f
    unless (usableRelevance frel || ctx == Irrel) $ do
      reportSDoc "tc.meta.occurs" 35 $ text ("relevance of projection: " ++ show frel)
      abort ctx $ MetaIrrelevantSolution m $ Def f []
    return e
  occurs red ctx m xs (Apply a) = Apply <$> occurs red ctx m xs a
  occurs red ctx m xs (IApply x y a)
    = IApply <$> occurs red ctx m xs x
             <*> occurs red ctx m xs y
             <*> occurs red ctx m xs a

  metaOccurs m (Proj{} ) = return ()
  metaOccurs m (Apply a) = metaOccurs m a
  metaOccurs m (IApply x y a) = metaOccurs m (x,(y,a))

instance (Occurs a, Subst t a) => Occurs (Abs a) where
  occurs red ctx m xs b@(Abs   s x) = Abs   s <$> underAbstraction_ b (occurs red ctx m (liftUnderAbs xs))
  occurs red ctx m xs b@(NoAbs s x) = NoAbs s <$> occurs red ctx m xs x

  metaOccurs m (Abs   s x) = metaOccurs m x
  metaOccurs m (NoAbs s x) = metaOccurs m x

instance Occurs a => Occurs (Arg a) where
  occurs red ctx m xs (Arg info x) | isIrrelevant info = Arg info <$>
    occurs red Irrel m (goIrrelevant xs) x
  occurs red ctx m xs (Arg info x) | isNonStrict info  = Arg info <$>
    occurs red ctx m (goNonStrict xs) x
  occurs red ctx m xs (Arg info x) = Arg info <$>
    occurs red ctx m xs x

  metaOccurs m a = metaOccurs m (unArg a)

instance Occurs a => Occurs (Dom a) where
  occurs red ctx m xs = traverse $ occurs red ctx m xs
  metaOccurs m = metaOccurs m . unDom

instance (Occurs a, Occurs b) => Occurs (a,b) where
  occurs red ctx m xs (x,y) = (,) <$> occurs red ctx m xs x <*> occurs red ctx m xs y

  metaOccurs m (x,y) = metaOccurs m x >> metaOccurs m y

instance Occurs a => Occurs [a] where
  occurs red ctx m xs ys = mapM (occurs red ctx m xs) ys

  metaOccurs m ys = mapM_ (metaOccurs m) ys

instance Occurs a => Occurs (Maybe a) where
  occurs red ctx m mx my = traverse (occurs red ctx m mx) my

  metaOccurs m = maybe (return ()) (metaOccurs m)

-- * Getting rid of flexible occurrences

-- | @prune m' vs xs@ attempts to remove all arguments from @vs@ whose
--   free variables are not contained in @xs@.
--   If successful, @m'@ is solved by the new, pruned meta variable and we
--   return @True@ else @False@.
--
--   Issue 1147:
--   If any of the meta args @vs@ is matchable, e.g., is a constructor term,
--   we cannot prune, because the offending variables could be removed by
--   reduction for a suitable instantiation of the meta variable.
prune :: MonadMetaSolver m => MetaId -> Args -> [Nat] -> m PruneResult
prune m' vs xs = do
  caseEitherM (runExceptT $ mapM (hasBadRigid xs) $ map unArg vs)
    (const $ return PrunedNothing) $ \ kills -> do
    reportSDoc "tc.meta.kill" 10 $ vcat
      [ "attempting kills"
      , nest 2 $ vcat
        [ "m'    =" <+> pretty m'
        , "xs    =" <+> prettyList (map (prettyTCM . var) xs)
        , "vs    =" <+> prettyList (map prettyTCM vs)
        , "kills =" <+> text (show kills)
        ]
      ]
    killArgs kills m'

-- | @hasBadRigid xs v = Just True@ iff one of the rigid variables in @v@ is not in @xs@.
--   Actually we can only prune if a bad variable is in the head. See issue 458.
--   Or in a non-eliminateable position (see succeed/PruningNonMillerPattern).
--
--   @hasBadRigid xs v = Nothing@ means that
--   we cannot prune at all as one of the meta args is matchable.
--   (See issue 1147.)
hasBadRigid :: (MonadReduce m, HasConstInfo m, MonadAddContext m)
            => [Nat] -> Term -> ExceptT () m Bool
hasBadRigid xs t = do
  -- We fail if we encounter a matchable argument.
  let failure = throwError ()
  tb <- reduceB t
  let t = ignoreBlocking tb
  case t of
    Var x _      -> return $ notElem x xs
    -- Issue 1153: A lambda has to be considered matchable.
    -- Lam _ v    -> hasBadRigid (0 : map (+1) xs) (absBody v)
    Lam _ v      -> failure
    DontCare v   -> hasBadRigid xs v
    -- The following types of arguments cannot be eliminated by a pattern
    -- match: data, record, Pi, levels, sorts
    -- Thus, their offending rigid variables are bad.
    v@(Def f es) -> ifNotM (isNeutral tb f es) failure $ {- else -} do
      lift $ es `rigidVarsNotContainedIn` xs
    -- Andreas, 2012-05-03: There is room for further improvement.
    -- We could also consider a defined f which is not blocked by a meta.
    Pi a b       -> lift $ (a,b) `rigidVarsNotContainedIn` xs
    Level v      -> lift $ v `rigidVarsNotContainedIn` xs
    Sort s       -> lift $ s `rigidVarsNotContainedIn` xs
    -- Since constructors can be eliminated by pattern-matching,
    -- offending variables under a constructor could be removed by
    -- the right instantiation of the meta variable.
    -- Thus, they are not rigid.
    Con c _ es | Just args <- allApplyElims es -> do
      ifM (isEtaCon (conName c))
        -- in case of a record con, we can in principle prune
        -- (but not this argument; the meta could become a projection!)
        (and <$> mapM (hasBadRigid xs . unArg) args)  -- not andM, we need to force the exceptions!
        failure
    Con c _ es | otherwise -> failure
    Lit{}        -> failure -- matchable
    MetaV{}      -> failure -- potentially matchable
    Dummy{}      -> return False

-- | Check whether a term @Def f es@ is finally stuck.
--   Currently, we give only a crude approximation.
isNeutral :: (HasConstInfo m) => Blocked t -> QName -> Elims -> m Bool
isNeutral b f es = do
  let yes = return True
      no  = return False
  def <- getConstInfo f
  if not (null $ defMatchable def) then no else do
  case theDef def of
    AbstractDefn{} -> yes
    Axiom{}    -> yes
    Datatype{} -> yes
    Record{}   -> yes
    Function{} -> case b of
      NotBlocked StuckOn{}   _ -> yes
      NotBlocked AbsurdMatch _ -> yes
      _                        -> no
    GeneralizableVar{} -> __IMPOSSIBLE__
    _          -> no

-- | Check whether any of the variables (given as de Bruijn indices)
--   occurs *definitely* in the term in a rigid position.
--   Reduces the term successively to remove variables in dead subterms.
--   This fixes issue 1386.
rigidVarsNotContainedIn
  :: (MonadReduce m, MonadAddContext m, MonadTCEnv m, MonadDebug m, AnyRigid a)
  => a -> [Nat] -> m Bool
rigidVarsNotContainedIn v is = do
  n0 <- getContextSize
  let -- allowed variables as de Bruijn levels
      levels = Set.fromList $ map (n0-1 -) is
      -- test if index is forbidden by converting it to level
      test i = do
        n <- getContextSize
        -- get de Bruijn level for i
        let l = n-1 - i
            -- If l >= n0 then it is a bound variable and can be
            -- ignored.  Otherwise, it has to be in the allowed levels.
            forbidden = l < n0 && not (l `Set.member` levels)
        when forbidden $
          reportSLn "tc.meta.kill" 20 $
            "found forbidden de Bruijn level " ++ show l
        return forbidden
  anyRigid test v

-- | Collect the *definitely* rigid variables in a monoid.
--   We need to successively reduce the expression to do this.

class AnyRigid a where
  anyRigid :: (MonadReduce tcm, MonadAddContext tcm)
           => (Nat -> tcm Bool) -> a -> tcm Bool

instance AnyRigid Term where
  anyRigid f t = do
    b <- reduceB t
    case ignoreBlocking b of
      -- Upon entry, we are in rigid position, thus,
      -- bound variables are rigid ones.
      Var i es   -> f i `or2M` anyRigid f es
      Lam _ t    -> anyRigid f t
      Lit{}      -> return False
      Def _ es   -> case b of
        -- If the definition is blocked by a meta, its arguments
        -- may be in flexible positions.
        Blocked{}                   -> return False
        -- If the definition is incomplete, arguments might disappear
        -- by reductions that come with more clauses, thus, these
        -- arguments are not rigid.
        NotBlocked MissingClauses _ -> return False
        -- _        -> mempty -- breaks: ImproveInertRHS, Issue442, PruneRecord, PruningNonMillerPattern
        _        -> anyRigid f es
      Con _ _ ts -> anyRigid f ts
      Pi a b     -> anyRigid f (a,b)
      Sort s     -> anyRigid f s
      Level l    -> anyRigid f l
      MetaV{}    -> return False
      DontCare{} -> return False
      Dummy{}    -> return False

instance AnyRigid Type where
  anyRigid f (El s t) = anyRigid f (s,t)

instance AnyRigid Sort where
  anyRigid f s =
    case s of
      Type l     -> fold l
      Prop l     -> fold l
      Inf        -> return False
      SizeUniv   -> return False
      PiSort s1 s2 -> return False
      UnivSort s -> fold s
      MetaS{}    -> return False
      DefS{}     -> return False
      DummyS{}   -> return False
    where fold = anyRigid f

instance AnyRigid Level where
  anyRigid f (Max ls) = anyRigid f ls

instance AnyRigid PlusLevel where
  anyRigid f ClosedLevel{} = return False
  anyRigid f (Plus _ l)    = anyRigid f l

instance AnyRigid LevelAtom where
  anyRigid f l =
    case l of
      MetaLevel{} -> return False
      NeutralLevel MissingClauses _ -> return False
      NeutralLevel _              l -> fold l
      BlockedLevel _              l -> fold l
      UnreducedLevel              l -> fold l
    where fold = anyRigid f

instance (Subst t a, AnyRigid a) => AnyRigid (Abs a) where
  anyRigid f b = underAbstraction_ b $ anyRigid f

instance AnyRigid a => AnyRigid (Arg a) where
  anyRigid f a =
    case getRelevance a of
      -- Irrelevant arguments are definitionally equal to
      -- values, so the variables there are not considered
      -- "definitely rigid".
      Irrelevant -> return False
      _          -> anyRigid f $ unArg a

instance AnyRigid a => AnyRigid (Dom a) where
  anyRigid f dom = anyRigid f $ unDom dom

instance AnyRigid a => AnyRigid (Elim' a) where
  anyRigid f (Apply a)      = anyRigid f a
  anyRigid f (IApply x y a) = anyRigid f (x,(y,a))
  anyRigid f Proj{}         = return False

instance AnyRigid a => AnyRigid [a] where
  anyRigid f xs = anyM xs $ anyRigid f

instance (AnyRigid a, AnyRigid b) => AnyRigid (a,b) where
  anyRigid f (a,b) = anyRigid f a `or2M` anyRigid f b


data PruneResult
  = NothingToPrune   -- ^ the kill list is empty or only @False@s
  | PrunedNothing    -- ^ there is no possible kill (because of type dep.)
  | PrunedSomething  -- ^ managed to kill some args in the list
  | PrunedEverything -- ^ all prescribed kills where performed
    deriving (Eq, Show)

-- | @killArgs [k1,...,kn] X@ prunes argument @i@ from metavar @X@ if @ki==True@.
--   Pruning is carried out whenever > 0 arguments can be pruned.
killArgs :: (MonadMetaSolver m) => [Bool] -> MetaId -> m PruneResult
killArgs kills _
  | not (or kills) = return NothingToPrune  -- nothing to kill
killArgs kills m = do
  mv <- lookupMeta m
  allowAssign <- asksTC envAssignMetas
  if mvFrozen mv == Frozen || not allowAssign then return PrunedNothing else do
      -- Andreas 2011-04-26, we allow pruning in MetaV and MetaS
      let a = jMetaType $ mvJudgement mv
      TelV tel b <- telView' <$> instantiateFull a
      let args         = zip (telToList tel) (kills ++ repeat False)
      (kills', a') <- killedType args b
      dbg kills' a a'
      -- If there is any prunable argument, perform the pruning
      if not (any unArg kills') then return PrunedNothing else do
        performKill kills' m a'
        -- Only successful if all occurrences were killed
        -- Andreas, 2011-05-09 more precisely, check that at least
        -- the in 'kills' prescribed kills were carried out
        return $ if (and $ zipWith implies kills $ map unArg kills')
                   then PrunedEverything
                   else PrunedSomething
  where
    implies :: Bool -> Bool -> Bool
    implies False _ = True
    implies True  x = x
    dbg kills' a a' =
      reportSDoc "tc.meta.kill" 10 $ vcat
        [ "after kill analysis"
        , nest 2 $ vcat
          [ "metavar =" <+> prettyTCM m
          , "kills   =" <+> text (show kills)
          , "kills'  =" <+> text (show kills')
          , "oldType =" <+> prettyTCM a
          , "newType =" <+> prettyTCM a'
          ]
        ]

-- | @killedType [((x1,a1),k1)..((xn,an),kn)] b = ([k'1..k'n],t')@
--   (ignoring @Dom@).  Let @t' = (xs:as) -> b@.
--   Invariant: @k'i == True@ iff @ki == True@ and pruning the @i@th argument from
--   type @b@ is possible without creating unbound variables.
--   @t'@ is type @t@ after pruning all @k'i==True@.
killedType :: (MonadReduce m) => [(Dom (ArgName, Type), Bool)] -> Type -> m ([Arg Bool], Type)
killedType args b = do

  -- Turn list of bools into an IntSet containing the variables we want to kill
  -- (indices relative to b).
  let tokill = IntSet.fromList [ i | ((_, True), i) <- zip (reverse args) [0..] ]

  -- First, check the free variables of b to see if they prevent any kills.
  (tokill, b) <- reallyNotFreeIn tokill b

  -- Then recurse over the telescope (right-to-left), building up the final type.
  (killed, b) <- go (reverse $ map fst args) tokill b

  -- Turn the IntSet of killed variables into the list of Arg Bool's to return.
  let kills = [ Arg (getArgInfo dom) (IntSet.member i killed)
              | (i, (dom, _)) <- reverse $ zip [0..] $ reverse args ]
  return (kills, b)
  where
    down = IntSet.map pred
    up   = IntSet.map succ

    -- go Δ xs B
    -- Invariants:
    --   - Δ ⊢ B
    --   - Δ is represented as a list in right-to-left order
    --   - xs are deBruijn indices into Δ
    --   - xs ∩ FV(B) = Ø
    -- Result: (ys, Δ' → B')
    --    where Δ' ⊆ Δ  (possibly reduced to remove dependencies, see #3177)
    --          ys ⊆ xs are the variables that were dropped from Δ
    --          B' = strengthen ys B
    go :: (MonadReduce m) => [Dom (ArgName, Type)] -> IntSet -> Type -> m (IntSet, Type)
    go [] xs b | IntSet.null xs = return (xs, b)
               | otherwise      = __IMPOSSIBLE__
    go (arg : args) xs b  -- go (Δ (x : A)) xs B, (x = deBruijn index 0)
      | IntSet.member 0 xs = do
          -- Case x ∈ xs. We know x ∉ FV(B), so we can safely drop x from the
          -- telescope. Drop x from xs (and shift indices) and recurse with
          -- `strengthen x B`.
          let ys = down (IntSet.delete 0 xs)
          (ys, b) <- go args ys $ strengthen __IMPOSSIBLE__ b
          -- We need to return a set of killed variables relative to Δ (x : A), so
          -- shift ys and add x back in.
          return (IntSet.insert 0 $ up ys, b)
      | otherwise = do
          -- Case x ∉ xs. We either can't or don't want to get rid of x. In
          -- this case we have to check A for potential dependencies preventing
          -- us from killing variables in xs.
          let xs'       = down xs -- Shift to make relative to Δ ⊢ A
              (name, a) = unDom arg
          (ys, a) <- reallyNotFreeIn xs' a
          -- Recurse on Δ, ys, and (x : A') → B, where A reduces to A' and ys ⊆ xs'
          -- not free in A'. We already know ys not free in B.
          (zs, b) <- go args ys (mkPi ((name, a) <$ arg) b)
          -- Shift back up to make it relative to Δ (x : A) again.
          return (up zs, b)

reallyNotFreeIn :: (MonadReduce m) => IntSet -> Type -> m (IntSet, Type)
reallyNotFreeIn xs a | IntSet.null xs = return (xs, a)  -- Shortcut
reallyNotFreeIn xs a = do
  let fvs      = freeVars a
      anywhere = allVars fvs
      rigid    = IntSet.unions [stronglyRigidVars fvs, unguardedVars fvs]
      nonrigid = IntSet.difference anywhere rigid
      hasNo    = IntSet.null . IntSet.intersection xs
  if | hasNo nonrigid ->
        -- No non-rigid occurrences. We can't do anything about the rigid
        -- occurrences so drop those and leave `a` untouched.
        return (IntSet.difference xs rigid, a)
     | otherwise -> do
        -- If there are non-rigid occurrences we need to reduce a to see if
        -- we can get rid of them (#3177).
        (fvs , a) <- forceNotFree (IntSet.difference xs rigid) a
        let xs = IntMap.keysSet $ IntMap.filter (== NotFree) fvs
        return (xs , a)

-- | Instantiate a meta variable with a new one that only takes
--   the arguments which are not pruneable.
performKill
  :: MonadMetaSolver m
  => [Arg Bool]    -- ^ Arguments to old meta var in left to right order
                   --   with @Bool@ indicating whether they can be pruned.
  -> MetaId        -- ^ The old meta var to receive pruning.
  -> Type          -- ^ The pruned type of the new meta var.
  -> m ()
performKill kills m a = do
  mv <- lookupMeta m
  when (mvFrozen mv == Frozen) __IMPOSSIBLE__
  -- Arity of the old meta.
  let n = size kills
  -- The permutation of the new meta picks the arguments
  -- which are not pruned in left to right order
  -- (de Bruijn level order).
  let perm = Perm n
             [ i | (i, Arg _ False) <- zip [0..] kills ]
      judg = case mvJudgement mv of
        HasType{} -> HasType __IMPOSSIBLE__ a
        IsSort{}  -> IsSort  __IMPOSSIBLE__ a
  m' <- newMeta Instantiable (mvInfo mv) (mvPriority mv) perm judg
  -- Andreas, 2010-10-15 eta expand new meta variable if necessary
  etaExpandMetaSafe m'
  let -- Arguments to new meta (de Bruijn indices)
      -- in left to right order.
      vars = [ Arg info (var i)
             | (i, Arg info False) <- zip (downFrom n) kills ]
      u       = MetaV m' $ map Apply vars
      -- Arguments to the old meta (just arg infos and name hints)
      -- in left to right order.
      tel     = map ("v" <$) kills
  dbg m' u
  assignTerm m tel u  -- m tel := u
  where
    dbg m' u = reportSDoc "tc.meta.kill" 10 $ vcat
      [ "actual killing"
      , nest 2 $ vcat
        [ "new meta:" <+> pretty m'
        , "kills   :" <+> text (show kills)
        , "inst    :" <+> pretty m <+> ":=" <+> prettyTCM u
        ]
      ]
